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

module Vickrey.BsDigits (
  BsDigits,
  bsDigits,
  encodeInteger
  ) where

import           Data.Aeson       (FromJSON, ToJSON)
import           GHC.Generics     (Generic)
import           Ledger.Typed.Tx
import qualified PlutusTx
import           PlutusTx.Prelude hiding (Semigroup (..), unless)
import qualified Prelude          hiding (head, max, tail)


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
  , bsMinus :: ByteString
  }
  deriving stock (Show, Generic, Prelude.Eq)
  deriving anyclass (ToJSON, FromJSON)

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
  , bsMinus = "-"
  }

{-# INLINABLE encodeInteger #-}
encodeInteger :: Integer -> BsDigits -> ByteString
encodeInteger val digits
  | val == 0  = bs0 digits
  | val > 0   = encodeInteger' val
  | otherwise = bsMinus digits `concatenate` encodeInteger' (negate val)
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
