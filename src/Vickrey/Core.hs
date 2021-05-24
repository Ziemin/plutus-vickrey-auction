{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Vickrey.Core where

import           Control.Monad                hiding (fmap)
import           Data.Aeson                   (FromJSON, ToJSON)
import qualified Data.Map                     as Map
import           Data.Monoid                  (Last (..))
import           Data.Text                    (Text, pack)
import           GHC.Generics                 (Generic)
import           Ledger                       hiding (singleton)
import           Ledger.Ada                   as Ada
import           Ledger.Constraints           as Constraints
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Value                 as Value
import           Plutus.Contract              as Contract hiding (when)
import           Plutus.Contract.StateMachine
import           Plutus.Contracts.Currency    as Currency
import qualified PlutusTx
import qualified PlutusTx.AssocMap            as AssocMap
import           PlutusTx.Prelude             hiding (Semigroup (..), unless)
import           Prelude                      (Semigroup (..))
import qualified Prelude                      as Prelude


data AuctionParams = AuctionParams
  { aOwner              :: !PubKeyHash
  , aAsset              :: !Value
  , aMaxNumParticipants :: !Integer
  , aMinPrice           :: !Value
  , aLockAmount         :: !Value
  , aBidDeadline        :: !Slot
  , aRevealDeadline     :: !Slot
  , aClaimDeadline      :: !Slot
  , aThreadToken        :: !AssetClass
  }
  deriving stock (Show, Generic, Prelude.Eq)
  deriving anyclass (ToJSON, FromJSON)


PlutusTx.makeLift ''AuctionParams


type SealedBids = AssocMap.Map PubKeyHash ByteString
type OpenBids = AssocMap.Map PubKeyHash Value

data AuctionState
  = Initializing
  | Collecting SealedBids
  | Revealing SealedBids OpenBids
  | Claiming
    { winner    :: !PubKeyHash,
      price     :: !PubKeyHash,
      unclaimed :: ![PubKeyHash]
    }
  | Finished
  deriving stock (Show, Generic, Prelude.Eq)
  deriving anyclass (ToJSON, FromJSON)

PlutusTx.unstableMakeIsData ''AuctionState

data AuctionAction
  = Init
  | PlaceBid { sealedBid :: ByteString, bidder :: PubKeyHash }
  | RevealBid { bid :: Value, bidder :: PubKeyHash, nonce :: ByteString }
  | Claim { bidder :: PubKeyHash }
  deriving stock (Show, Generic, Prelude.Eq)
  deriving anyclass (ToJSON, FromJSON)

PlutusTx.unstableMakeIsData ''AuctionAction


{-# INLINABLE valueHash #-}
valueHash :: Value -> ByteString
valueHash val =
  let DatumHash hash = datumHash (Datum $ PlutusTx.toData val)
  in hash

{-# INLINABLE encodeBid #-}
encodeBid :: Value -> ByteString -> ByteString
encodeBid val nonce = sha2_256 (nonce `concatenate` valueHash val)

{-# INLINEABLE validRevealBid #-}
validRevealBid :: SealedBids -> AuctionAction -> Bool
validRevealBid sealedBids RevealBid{bid, bidder, nonce} =
  let maybeSealedBid = AssocMap.lookup bidder sealedBids
  in maybe False ((encodeBid bid nonce) ==) maybeSealedBid
validRevealBid _          _                               = False


{-# INLINEABLE validRevealBid #-}
winnerAndPrice :: AuctionParams -> OpenBids -> (PubKeyHash, Value)
winnerAndPrice auction bids = case AssocMap.toList of
  []            -> (aOwner auction, mempty)     -- the owner is the winner
  [(bidder, _)] -> (bidder, aMinPrice auction)  -- single participant pays the min price
  -- bidList       ->
  --   let ord

{-# INLINABLE auctionTransition #-}
auctionTransition :: AuctionParams -> State AuctionState -> AuctionAction -> Maybe (TxConstraints Void Void, State AuctionState)
auctionTransition auction State{stateData=oldState, stateValue=currentValue} action
  = case (oldState, action) of
      -- Auction initialization
      (Initializing, Init)
          -> let constraints = Constraints.mustBeSignedBy (aOwner auction)                <>
                               Constraints.mustValidateIn (to $ aBidDeadline auction - 1)
             in Just ( constraints
                     , State
                       { stateData = Collecting AssocMap.empty
                       , stateValue = aAsset auction
                       }
                     )

      -- Bidding
      (Collecting bids, PlaceBid{sealedBid, bidder})
        | length (AssocMap.toList bids) < aMaxNumParticipants auction && -- is there a place for new bidders
          not (AssocMap.member bidder bids)                           && -- has not given their bid yet
          bidder /= aOwner auction                                       -- auction owner is not taking part in bidding

          -> let constraints = Constraints.mustBeSignedBy bidder                      <>
                               Constraints.mustValidateIn (to $ aBidDeadline auction)
             in Just ( constraints
                     , State
                       { stateData = Collecting (AssocMap.insert bidder sealedBid bids)
                       , stateValue = currentValue <> aLockAmount auction
                       }
                    )

      -- Transition from Bidding to Revealing
      (Collecting sealedBids, b@RevealBid{bid, bidder})
        | validRevealBid sealedBids b &&  -- bidder has not revelead their bid yet
          bid `geq` aMinPrice auction     -- bid is at least as high as minimum price
          -> let constraints = Constraints.mustBeSignedBy bidder                      <>
                               Constraints.mustValidateIn (interval (aBidDeadline auction + 1) (aRevealDeadline auction))
             in Just ( constraints
                     , State
                       { stateData = Revealing (AssocMap.delete bidder sealedBids) (AssocMap.singleton bidder bid)
                       , stateValue = currentValue
                       }
                    )

      -- Revealing bids
      (Revealing sealedBids openBids, b@RevealBid{bid, bidder})
        | validRevealBid sealedBids b &&  -- bidder has not revelead their bid yet
          bid `geq` aMinPrice auction     -- bid is at least as high as minimum price

          -> let constraints = Constraints.mustBeSignedBy bidder                         <>
                               Constraints.mustValidateIn (to $ aRevealDeadline auction)
             in Just ( constraints
                     , State
                       { stateData = Revealing (AssocMap.delete bidder sealedBids) (AssocMap.insert bidder bid openBids)
                       , stateValue = currentValue
                       }
                     )

      -- Transition from Revealing to Claiming
      (Revealing sealedBids openBids, Claim bidder)
        | True
        -> Nothing

      -- Claiming

      -- Transition from Claiming to Finished

      -- Everything Else
      _   -> Nothing


{-# INLINABLE isFinished #-}
isFinished :: AuctionState -> Bool
isFinished Finished = True
isFinished _        = False
