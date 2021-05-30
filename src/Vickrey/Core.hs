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
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Vickrey.Core (
  AuctionParams(..),
  SealedBids,
  OpenBids,
  AuctionState(..),
  AuctionAction(..),
  OwnerParams(..),
  BidderParams(..),
  AuctionSchema,
  endpoints
  ) where

import           Control.Monad                hiding (fmap)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Text                    (Text, pack)
import           GHC.Generics                 (Generic)
import           Ledger                       hiding (singleton)
import           Ledger.Ada                   as Ada hiding (divide)
import           Ledger.Constraints           as Constraints
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Typed.Tx
import           Ledger.Value                 as Value
import           Playground.Contract          (ToSchema)
import           Plutus.Contract              as Contract hiding (when)
import           Plutus.Contract.StateMachine
import qualified PlutusTx
import qualified PlutusTx.AssocMap            as AssocMap
import qualified PlutusTx.List                as List
import           PlutusTx.Prelude             hiding (Semigroup (..), unless)
import           Prelude                      (Semigroup (..))
import qualified Prelude                      hiding (head, max, tail)

import           Vickrey.BsDigits

data AuctionParams = AuctionParams
  { aOwner              :: !PubKeyHash
  , aAsset              :: !Value
  , aMaxNumParticipants :: !Integer
  , aMinPrice           :: !Ada
  , aLockAmount         :: !Ada
  , aBidDeadline        :: !Slot
  , aRevealDeadline     :: !Slot
  , aClaimDeadline      :: !Slot
  , aThreadToken        :: !AssetClass
  , aBsDigits           :: !BsDigits
  }
  deriving stock (Show, Generic, Prelude.Eq)
  deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeLift ''AuctionParams


type SealedBids = AssocMap.Map PubKeyHash ByteString
type OpenBids = AssocMap.Map PubKeyHash Ada


data AuctionState
  = Collecting SealedBids
  | Revealing SealedBids OpenBids
  | Claiming
    { winner     :: !PubKeyHash
    , price      :: !Ada
    , unclaimed  :: ![PubKeyHash]
    , unrevealed :: Integer
    }
  | Finished
    { winner :: !PubKeyHash
    , price  :: !Ada
    }
  deriving stock (Show, Generic, Prelude.Eq)
  deriving anyclass (ToJSON, FromJSON)

PlutusTx.unstableMakeIsData ''AuctionState


data AuctionAction
  = PlaceBid { sealedBid :: ByteString, bidder :: PubKeyHash }
  | RevealBid { bid :: Ada, bidder :: PubKeyHash, nonce :: ByteString }
  | Claim { bidder :: PubKeyHash }
  deriving stock (Show, Generic, Prelude.Eq)
  deriving anyclass (ToJSON, FromJSON)

PlutusTx.unstableMakeIsData ''AuctionAction


{-# INLINABLE bidHash #-}
bidHash :: Ada -> BsDigits -> ByteString
bidHash bid digits = sha2_256 $ encodeInteger (getLovelace bid) digits

{-# INLINABLE encodeBid #-}
encodeBid :: Ada -> ByteString -> BsDigits -> ByteString
encodeBid bid nonce digits = nonce `concatenate` bidHash bid digits

{-# INLINEABLE validRevealBid #-}
validRevealBid :: SealedBids -> AuctionAction -> BsDigits -> Bool
validRevealBid sealedBids RevealBid{bid, bidder, nonce} digits =
   AssocMap.lookup bidder sealedBids == Just (encodeBid bid nonce digits)
validRevealBid _          _                             _ = False

{-# INLINEABLE winnerAndPrice #-}
winnerAndPrice :: AuctionParams -> OpenBids -> (PubKeyHash, Ada)
winnerAndPrice auction bids = case AssocMap.toList bids of
  []            -> (aOwner auction, 0)          -- the owner is the winner
  [(bidder, _)] -> (bidder, aMinPrice auction)  -- single participant pays the min price
  _             ->
    let
      (winner, _)      = getMaxBid . AssocMap.toList $ bids
      (_, secondPrice) = getMaxBid . AssocMap.toList $ AssocMap.delete winner bids
    in (winner, secondPrice)
    where
      getMaxBid (b:bs) = foldl max' b bs

      max' b1@(_, bid1) b2@(_, bid2)
        | bid1 >= bid2 = b1
        | otherwise    = b2


{-# INLINABLE auctionTransition #-}
auctionTransition :: AuctionParams -> State AuctionState -> AuctionAction -> Maybe (TxConstraints Void Void, State AuctionState)
auctionTransition auction State{stateData=oldState} action = case (oldState, action) of
      -- Bidding
      (Collecting bids, PlaceBid{sealedBid, bidder})
        | length (AssocMap.toList bids) < aMaxNumParticipants auction && -- is there a place for new bidders
          not (AssocMap.member bidder bids)                           && -- has not given their bid yet
          bidder /= aOwner auction                                       -- auction owner is not taking part in bidding

          -> let constraints =
                   Constraints.mustBeSignedBy bidder
                   <> Constraints.mustValidateIn (to $ aBidDeadline auction) -- bids have to be places before the bidding deadline
             in Just ( constraints
                     , State
                       { stateData = Collecting (AssocMap.insert bidder sealedBid bids) -- add valid bidinto sealed bids
                       , stateValue = aAsset auction
                                      <> Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * length bids) -- other bidder have locked their funds
                                      <> Ada.toValue (aLockAmount auction) -- bidder has to lock certain amount in the script to participate
                       }
                    )

      -- Transition from Bidding to Revealing
      (Collecting sealedBids, b@RevealBid{bid, bidder})
        | validRevealBid sealedBids b (aBsDigits auction) && -- bidder has not revelead their bid yet and their bid was properly encoded
          bid >= aMinPrice auction                           -- bid is at least as high as minimum price

          -> let constraints =
                   Constraints.mustBeSignedBy bidder <>
                   Constraints.mustValidateIn (interval (aBidDeadline auction + 1) (aRevealDeadline auction)) -- revealing happens in the revealing period
             in Just ( constraints
                     , State
                       { stateData = Revealing (AssocMap.delete bidder sealedBids) (AssocMap.singleton bidder bid) -- the bid is moved to open bids
                       , stateValue = aAsset auction
                                      <> Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * length sealedBids)
                       }
                    )

      -- No bidders appeared nor revelaed their bids before deadline
      (Collecting bids, Claim bidder)
        | bidder == aOwner auction

          -> let constraints =
                   Constraints.mustBeSignedBy bidder
                   <> Constraints.mustPayToPubKey (aOwner auction) (aAsset auction) -- owner gets their asset back
                   <> Constraints.mustValidateIn (
                        if null bids then
                          from $ aBidDeadline auction + 1 -- when there are no bidders the owner can claim their assets earlier
                        else
                          from $ aRevealDeadline auction + 1 -- otherwise it can only happen after the revelations
                        )
             in Just ( constraints
                     , State
                       { stateData = Finished (aOwner auction) 0
                       , stateValue = Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * length bids) -- bidder who do not reveal their bids on time lose their locked assets forever
                       }
                    )

      -- Revealing bids
      (Revealing sealedBids openBids, b@RevealBid{bid, bidder})
        | validRevealBid sealedBids b (aBsDigits auction) &&  -- bidder has not revelead their bid yet and their bid was properly encoded
          bid >= aMinPrice auction                            -- bid is at least as high as the minimum price

          -> let constraints =
                   Constraints.mustBeSignedBy bidder
                   <> Constraints.mustValidateIn (to $ aRevealDeadline auction)  -- revealing has to happen before the deadline
             in Just ( constraints
                     , State
                       { stateData = Revealing (AssocMap.delete bidder sealedBids) (AssocMap.insert bidder bid openBids) -- move the bidder to open bids
                       , stateValue = aAsset auction
                                      <> Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * (length sealedBids + length openBids))
                       }
                     )

      -- Transition from Revealing to Claiming/Finished
      (Revealing sealedBids openBids, Claim bidder)
        -- winner is retrieving the asset
        | bidder == winner
          -> let specificConstraints =
                   Constraints.mustPayToPubKey winner (aAsset auction)  -- winner is getting the asset
                   <> Constraints.mustPayToPubKey (aOwner auction) (Ada.toValue price) -- auction owner is paid the asset price
                   <> mconcat [ Constraints.mustPayToPubKey bidder' payBack  -- bidders who revealed their bids are getting their locked funds back
                              | bidder' <- AssocMap.keys openBids
                              ]
             in Just ( commonConstraints <> specificConstraints
                     , State
                       { stateData  = Finished winner price
                       , stateValue = Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * unrevealed) -- bidders who do not reveal their bids lose their locked funds forever
                       }
                     )

        -- 'loser' is getting their locked funds back
        | bidder `AssocMap.member` openBids
          -> let
               specificConstraints =
                 mconcat [ Constraints.mustPayToPubKey bidder' payBack -- all of the 'losers' are getting their locked funds back
                         | bidder' <- AssocMap.keys openBids
                         , bidder' /= winner -- the winner still has to pay for the asset
                         ]
             in Just ( commonConstraints <> specificConstraints
                     , State
                       { stateData  = Claiming winner price [winner] unrevealed
                       , stateValue = aAsset auction
                                      <> Ada.toValue (aLockAmount auction) -- winner's funds are locked
                                      <> Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * unrevealed)
                       }
                     )

        -- winner has not claimed the asset
        | bidder == aOwner auction
          -> let specificConstraints =
                   Constraints.mustPayToPubKey (aOwner auction) (aAsset auction)
                   <> Constraints.mustValidateIn (from $ aClaimDeadline auction + 1) -- after the deadline the owner is retrieving their assets
                   <> mconcat [ Constraints.mustPayToPubKey bidder' payBack -- bidder who revelaed their choices get their funds back
                              | bidder' <- AssocMap.keys openBids]
             in Just ( commonConstraints <> specificConstraints
                     , State
                       { stateData = Finished (aOwner auction) 0  -- the final winner is the owner
                       , stateValue = Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * unrevealed)
                       }
                     )


        where
          unrevealed        = length sealedBids
          (winner, price)   = winnerAndPrice auction openBids
          payBack           = Ada.toValue (aLockAmount auction)
          commonConstraints = Constraints.mustBeSignedBy bidder <>
                              Constraints.mustValidateIn (interval (aRevealDeadline auction + 1) (aClaimDeadline auction))

      -- Claiming
      (Claiming winner price unclaimed unrevealed, Claim bidder)
        -- winner is retrieving the asset
        | bidder == winner
          -> let specificConstraints =
                   Constraints.mustPayToPubKey winner (aAsset auction)  -- winner gets the asset
                   <> Constraints.mustPayToPubKey (aOwner auction) (Ada.toValue price) -- owner is paid the price
                   <> mconcat [ Constraints.mustPayToPubKey bidder' payBack -- 'losers' get their locked funds back
                              | bidder' <- unclaimed
                              ]
                   <> Constraints.mustValidateIn (
                        if bidder == aOwner auction then
                          always -- there is actually no winner the the moment of claiming, so the owner is retrieving their funds back at any time
                        else
                          to $ aClaimDeadline auction  -- otherwise the 'real' winner has to claim the asset before the deadline
                        )
             in Just ( commonConstraints <> specificConstraints
                     , State
                       { stateData  = Finished winner price
                       , stateValue = Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * unrevealed) -- the funds of unrevealed bids stay locked forever
                       }
                     )

        -- 'loser' is getting their locked funds back
        | isJust (List.findIndex (bidder ==) unclaimed)
          -> let
               specificConstraints =
                 Constraints.mustValidateIn (to $ aClaimDeadline auction)
                 <> mconcat [ Constraints.mustPayToPubKey bidder' payBack  -- all the 'losers' are getting back their locked funds
                            | bidder' <- unclaimed
                            , bidder' /= winner -- winner has to pay for the asset
                            ]
             in Just ( commonConstraints <> specificConstraints
                     , State
                       { stateData  = Claiming winner price [winner] unrevealed -- the winner still has to pay for the asset
                       , stateValue = aAsset auction
                                      <> Ada.toValue (aLockAmount auction) -- winner's funds are locked
                                      <> Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * unrevealed)
                       }
                     )

        -- winner has not claimed the asset
        | bidder == aOwner auction
          -> let specificConstraints =
                   Constraints.mustPayToPubKey (aOwner auction) (aAsset auction)
                   <> Constraints.mustValidateIn (from $ aClaimDeadline auction + 1) -- after the deadline the owner is retrieving their assets
                   <> mconcat [ Constraints.mustPayToPubKey bidder' payBack -- bidder who revelaed their choices get their funds back
                              | bidder' <- unclaimed ]
             in Just ( commonConstraints <> specificConstraints
                     , State
                       { stateData = Finished (aOwner auction) 0  -- the final winner is the owner
                       , stateValue = Ada.lovelaceValueOf (getLovelace (aLockAmount auction) * unrevealed)
                       }
                     )

        where
          payBack           = Ada.toValue (aLockAmount auction)
          commonConstraints = Constraints.mustBeSignedBy bidder

      -- Everything Else
      _   -> Nothing

type AuctionStateMachine = StateMachine AuctionState AuctionAction

{-# INLINABLE auctionStateMachine #-}
auctionStateMachine :: AuctionParams -> AuctionStateMachine
auctionStateMachine auction
  = mkStateMachine (Just $ aThreadToken auction) (auctionTransition auction) isFinal
  where
    isFinal :: AuctionState -> Bool
    isFinal = const False

{-# INLINABLE mkAuctionValidator #-}
mkAuctionValidator :: AuctionParams -> AuctionState -> AuctionAction -> ScriptContext -> Bool
mkAuctionValidator = mkValidator . auctionStateMachine

auctionInst :: AuctionParams -> Scripts.ScriptInstance AuctionStateMachine
auctionInst auction = Scripts.validator @AuctionStateMachine
    ($$(PlutusTx.compile [|| mkAuctionValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode auction)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @AuctionState @AuctionAction

auctionValidator :: AuctionParams -> Validator
auctionValidator = Scripts.validatorScript  . auctionInst

auctionAddress :: AuctionParams -> Ledger.Address
auctionAddress = scriptAddress . auctionValidator

auctionClient :: AuctionParams -> StateMachineClient AuctionState AuctionAction
auctionClient auction = mkStateMachineClient $ StateMachineInstance (auctionStateMachine auction) (auctionInst auction)


mapError' :: Contract w s SMContractError a -> Contract w s Text a
mapError' = mapError $ pack . show

getAuctionState ::
  forall w s. HasBlockchainActions s =>
  StateMachineClient AuctionState AuctionAction -> Contract w s Text AuctionState
getAuctionState client = do
  st <- mapError' $ getOnChainState client
  case st of
    Nothing          -> throwError "Auction not found"
    Just ((o, _), _) -> return $ tyTxOutData o

getAuctionStateMaybe ::
  forall w s. HasBlockchainActions s =>
  StateMachineClient AuctionState AuctionAction -> Contract w s Text (Maybe AuctionState)
getAuctionStateMaybe client = do
  st <- mapError' $ getOnChainState client
  case st of
    Nothing          -> return Nothing
    Just ((o, _), _) -> return $ Just (tyTxOutData o)


data OwnerParams = OwnerParams
    { opAsset               :: !Value
    , opMaxNumParticipants  :: !Integer
    , opMinPrice            :: !Ada
    , opLockAmount          :: !Ada
    , opBidDeadline         :: !Slot
    , opRevealDeadline      :: !Slot
    , opClaimDeadline       :: !Slot
    , opThreadTokenCurrency :: !CurrencySymbol
    , opThreadTokenName     :: !TokenName
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)


mkAuctionParams :: OwnerParams -> PubKeyHash -> AuctionParams
mkAuctionParams op owner
  = AuctionParams
    { aOwner              = owner
    , aAsset              = opAsset op
    , aMaxNumParticipants = opMaxNumParticipants op
    , aMinPrice           = opMinPrice op
    , aLockAmount         = opLockAmount op
    , aBidDeadline        = opBidDeadline op
    , aRevealDeadline     = opRevealDeadline op
    , aClaimDeadline      = opClaimDeadline op
    , aThreadToken        = AssetClass (opThreadTokenCurrency op, opThreadTokenName op)
    , aBsDigits           = bsDigits
    }


runAuction :: forall w s. HasBlockchainActions s => OwnerParams -> Contract w s Text ()
runAuction op = do
  pkh <- pubKeyHash <$> Contract.ownPubKey

  let auction = mkAuctionParams op pkh
      client  = auctionClient auction

  void $ mapError' $ runInitialise client (Collecting AssocMap.empty) (opAsset op)
  logInfo @String $ "Started auction: " ++ show auction

  void $ awaitSlot (opBidDeadline op + 1)
  getAuctionState client >>= \case

    Collecting sealedBids | null sealedBids -> do
      logInfo @String "No bidders. Closing auction..."
      void $ mapError' $ runStep client (Claim pkh)
      logInfo @String "Owner reclaimed their asset"

    _ -> do
      void $ awaitSlot (opRevealDeadline op + 1)
      getAuctionState client >>= \case

        Collecting {} -> do
          logInfo @String "No revealed bids. Closing auction..."
          void $ mapError' $ runStep client (Claim pkh)
          logInfo @String "Owner reclaimed their asset"

        _ -> do
          void $ awaitSlot (opClaimDeadline op + 1)
          getAuctionState client >>= \case

            Revealing {} -> do
              logInfo @String "No claims to assets. Closing auction..."
              void $ mapError' $ runStep client (Claim pkh)
              logInfo @String "Owner reclaimed their asset"

            Claiming {winner, price} -> do
              logInfo @String $ "Winner " ++ show winner ++ " did not claim the asset for "
                                ++ show price ++ ". Closing auction..."
              void $ mapError' $ runStep client (Claim pkh)
              logInfo @String "Owner reclaimed their asset"

            Finished winner price -> do
              logInfo @String $
                "Auction is finished. The winner " ++ show winner ++ " paid " ++ show price ++ "Ada."


data BidderParams = BidderParams
    { bdOwner       :: !PubKeyHash
    , bdOwnerParams :: !OwnerParams
    , bdBid         :: !Ada
    , bdNonce       :: !ByteString
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)


performBidding ::
  forall w s. HasBlockchainActions s =>
  StateMachineClient AuctionState AuctionAction ->
  BidderParams ->
  AuctionParams ->
  Contract w s Text ()
performBidding client bp auction = do
  pkh <- pubKeyHash <$> Contract.ownPubKey

  let bid       = bdBid bp
      nonce     = bdNonce bp
      sealedBid = encodeBid bid nonce (aBsDigits auction)

  logInfo @String "Placing sealed bid"
  void $ mapError' $ runStep client (PlaceBid sealedBid pkh)

  void $ awaitSlot (aBidDeadline auction + 1)
  logInfo @String "Revealing bid"
  void $ mapError' $ runStep client (RevealBid bid pkh nonce)

  void $ awaitSlot (aRevealDeadline auction + 1)
  logInfo @String "Claiming"
  void $ mapError' $ runStep client (Claim pkh)

  getAuctionState client >>= \case
    Finished winner price ->
      if winner == pkh then void $ logInfo $ "Won the auction for " ++ show price ++ " ADA"
      else void $ logInfo $ "Lost the auction. The price paid was " ++ show price ++ " ADA"

    _ -> throwError "Invalid auction state"


makeBid :: forall w s. HasBlockchainActions s => BidderParams -> Contract w s Text ()
makeBid bp = do
  let op        = bdOwnerParams bp
      auction   = mkAuctionParams op (bdOwner bp)
      client    = auctionClient auction

  when (bdBid bp < opMinPrice op)
    (throwError "Bid is lower than the min price")

  slot <- currentSlot
  when (slot >= opBidDeadline op)
    (throwError "Too late to make a bid")

  getAuctionStateMaybe client >>= \case

    Nothing -> mapError' (waitForUpdateUntil client (opBidDeadline op)) >>= \case
        WaitingResult Collecting {} -> performBidding client bp auction
        _                           -> logWarn @String "Auction has not started"

    Just _ -> performBidding client bp auction


type AuctionSchema = BlockchainActions
  .\/ Endpoint "runAuction" OwnerParams
  .\/ Endpoint "makeBid" BidderParams


endpoints :: Contract () AuctionSchema Text ()
endpoints = (run `select` bid) >> endpoints
  where
    run = endpoint @"runAuction" >>= runAuction
    bid = endpoint @"makeBid" >>= makeBid
