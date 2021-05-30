{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE NumericUnderscores         #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}


module Vickrey.Trace where

import           Control.Monad              hiding (fmap)
import           Control.Monad.Freer.Extras as Extras
import           Data.Default               (Default (..))
import qualified Data.Map                   as Map
import           Ledger
import           Ledger.Ada                 as Ada
import           Ledger.Value
import           Plutus.Trace.Emulator      as Emulator
import           PlutusTx.Prelude           hiding (mapM)
import           Wallet.Emulator.Wallet

import           Vickrey.Core

auctionAssetCurrency :: CurrencySymbol
auctionAssetCurrency = "ff"

auctionAssetTokenName :: TokenName
auctionAssetTokenName = "AUCTION_TOKEN"

auctionAsset :: Value
auctionAsset = assetClassValue (AssetClass (auctionAssetCurrency, auctionAssetTokenName)) 1

threadAssetCurrency :: CurrencySymbol
threadAssetCurrency = "dd"

threadAssetTokenName :: TokenName
threadAssetTokenName = "THREAD_TOKEN"

threadAsset :: Value
threadAsset = assetClassValue (AssetClass (threadAssetCurrency, threadAssetTokenName)) 1

maxParticipants :: Integer
maxParticipants = 10


auctionTrace :: Wallet -> [(Wallet, Ada, ByteString)] -> EmulatorTrace ()
auctionTrace owner bidders = do
  Extras.logInfo $ "Starting auction with owner: " ++ show owner ++ " and bidders: " ++ show bidders
  o <- activateContractWallet owner ownerEndpoints
  let pkhOwner = pubKeyHash $ walletPubKey owner
      op = OwnerParams
          { opAsset               = auctionAsset
          , opMaxNumParticipants  = maxParticipants
          , opMinPrice            = 1000
          , opLockAmount          = 100
          , opBidDeadline         = 10
          , opRevealDeadline      = 20
          , opClaimDeadline       = 30
          , opThreadTokenCurrency = threadAssetCurrency
          , opThreadTokenName     = threadAssetTokenName
          }

      getEndpoint (w, bid, nonce) = activateContractWallet w (bidderEndpoints bp)
        where bp = BidderParams
                { bdOwner       = pkhOwner
                , bdOwnerParams = op
                , bdBid         = bid
                , bdNonce       = nonce
                }

      placeBidAndWait h = callEndpoint @"place bid" h () >> void (Emulator.waitNSlots 1)
      revealBidAndWait h = callEndpoint @"reveal bid" h () >> void (Emulator.waitNSlots 1)
      claimAndWait h = callEndpoint @"claim" h () >> void (Emulator.waitNSlots 1)

  hs <- mapM getEndpoint bidders

  callEndpoint @"run auction" o op
  void $ Emulator.waitNSlots 2

  mapM_ placeBidAndWait hs

  void $ Emulator.waitUntilSlot (opBidDeadline op + 1)
  mapM_ revealBidAndWait hs

  void $ Emulator.waitUntilSlot (opRevealDeadline op + 1)
  mapM_ claimAndWait hs


test' :: Wallet -> [(Wallet, Ada, ByteString)] -> IO ()
test' owner bidders = runEmulatorTraceIO' def emCfg $ auctionTrace owner bidders
  where
    emCfg :: EmulatorConfig
    emCfg = EmulatorConfig $ Left $ Map.fromList $
      (owner, v <> auctionAsset <> threadAsset):[(w, v) | (w, _, _) <- bidders]

    v :: Value
    v = Ada.lovelaceValueOf 1000_000

test :: IO ()
test = do
  test' (Wallet 1) []
  test' (Wallet 1) [ (Wallet 2, 500, "Something")
                   ]
  test' (Wallet 1) [ (Wallet 2, 2000, "Something")
                   , (Wallet 3, 3000, "Secret")
                   , (Wallet 4, 2500, "Word")
                   , (Wallet 5, 2700, "Random")
                   , (Wallet 6, 700, "Stupid")
                   ]
