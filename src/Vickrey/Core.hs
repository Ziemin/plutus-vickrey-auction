{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Vickrey.Core where

-- import           Control.Monad                hiding (fmap)
import           Data.Aeson                   (FromJSON, ToJSON)
-- import qualified Data.Map                     as Map
-- import           Data.Monoid                  (Last (..))
-- import           Data.Text                    (Text, pack)
import           GHC.Generics                 (Generic)
import           Ledger                       hiding (singleton)
import           Ledger.Ada                   as Ada hiding (divide)
import           Ledger.Constraints           as Constraints
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Value                 as Value
-- import           Ledger.Ada                   as Ada
-- import           Plutus.Contract              as Contract hiding (when)
import           Plutus.Contract.StateMachine
-- import           Plutus.Contracts.Currency    as Currency
import qualified PlutusTx
import qualified PlutusTx.AssocMap            as AssocMap
import           PlutusTx.Prelude             hiding (Semigroup (..), unless)
-- import           PlutusTx.Ord                 (Ord, compare)
import           Prelude                      (Semigroup (..))
import qualified Prelude


data BsDigits = BsDigits
  { bs0     :: ByteString
  , bs1     :: ByteString
  , bs2     :: ByteString
  , bs3     :: ByteString
  , bs4     :: ByteString
  , bs5     :: ByteString
  , bs6     :: ByteString
  , bs7     :: ByteString
  , bs8     :: ByteString
  , bs9     :: ByteString
  , bsOther :: ByteString
  }
  deriving stock (Show, Generic, Prelude.Eq)
  deriving anyclass (ToJSON, FromJSON)

PlutusTx.unstableMakeIsData ''BsDigits
PlutusTx.makeLift ''BsDigits

bsDigits :: BsDigits
bsDigits = BsDigits
  { bs0 = "0"
  , bs1 = "1"
  , bs2 = "2"
  , bs3 = "3"
  , bs4 = "4"
  , bs5 = "5"
  , bs6 = "6"
  , bs7 = "7"
  , bs8 = "8"
  , bs9 = "9"
  , bsOther = "?"
  }

{-# INLINABLE encodeInteger #-}
encodeInteger :: Integer -> BsDigits -> ByteString
encodeInteger val digits = if val == 0 then bs0 digits else encodeInteger' val
  where
    encodeDigit :: Integer -> ByteString
    encodeDigit d
      | d == 0    = bs0 digits
      | d == 1    = bs1 digits
      | d == 2    = bs2 digits
      | d == 3    = bs3 digits
      | d == 4    = bs4 digits
      | d == 5    = bs5 digits
      | d == 6    = bs6 digits
      | d == 7    = bs7 digits
      | d == 8    = bs8 digits
      | d == 9    = bs9 digits
      | otherwise = bsOther digits

    encodeInteger' :: Integer -> ByteString
    encodeInteger' v
      | v == 0    = emptyByteString
      | otherwise = encodeInteger' (v `divide` 10) `concatenate` encodeDigit (v `modulo` 10)


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

newtype PkBid = PkBid { getBid :: (PubKeyHash, Ada) }
  deriving stock (Show, Generic, Prelude.Eq)
  deriving newtype (Eq)
  deriving anyclass (ToJSON, FromJSON)

instance Ord PkBid where
  {-# INLINEABLE compare #-}
  bid1 `compare` bid2 = snd (getBid bid1) `compare` snd (getBid bid2)


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
  let maybeSealedBid = AssocMap.lookup bidder sealedBids
  in maybe False ((encodeBid bid nonce digits) ==) maybeSealedBid
validRevealBid _          _                             _ = False

{-# INLINEABLE winnerAndPrice #-}
winnerAndPrice :: AuctionParams -> OpenBids -> (PubKeyHash, Ada)
winnerAndPrice auction bids = case AssocMap.toList bids of
  []            -> (aOwner auction, 0)          -- the owner is the winner
  [(bidder, _)] -> (bidder, aMinPrice auction)  -- single participant pays the min price
  _             ->
    let
      (winner, _)      = getBid . getMaxBid . toPkBidList $ bids
      (_, secondPrice) = getBid . getMaxBid . toPkBidList $ AssocMap.delete winner bids
    in (winner, secondPrice)
    where
      toPkBidList = map PkBid . AssocMap.toList

      getMaxBid list = foldr max (head list) (tail list)


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
                       , stateValue = currentValue <> Ada.toValue (aLockAmount auction)
                       }
                    )

      -- Transition from Bidding to Revealing
      (Collecting sealedBids, b@RevealBid{bid, bidder})
        | validRevealBid sealedBids b (aBsDigits auction) &&  -- bidder has not revelead their bid yet
          bid >= aMinPrice auction        -- bid is at least as high as minimum price
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
        | validRevealBid sealedBids b (aBsDigits auction) &&  -- bidder has not revelead their bid yet
          bid >= aMinPrice auction                            -- bid is at least as high as minimum price

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


{-# INLINABLE isFinal #-}
isFinal :: AuctionState -> Bool
isFinal Finished = True
isFinal _        = False

{-# INLINABLE checkStateAndAction #-}
checkStateAndAction :: AuctionState -> AuctionAction -> ScriptContext -> Bool
checkStateAndAction _ _ _ = True

type AuctionStateMachine = StateMachine AuctionState AuctionAction

{-# INLINABLE auctionStateMachine #-}
auctionStateMachine :: AuctionParams -> AuctionStateMachine
auctionStateMachine auction = StateMachine
    { smTransition  = auctionTransition auction
    , smFinal       = isFinal
    , smCheck       = checkStateAndAction
    , smThreadToken = Just $ aThreadToken auction
    }

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
