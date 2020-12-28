-- |
-- Module      :  Phonetic.Languages.Simplified.DataG
-- Copyright   :  (c) OleksandrZhabenko 2020
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  olexandr543@yahoo.com
--
-- Simplified version of the @phonetic-languages-common@ and @phonetic-languages-general@ packages.


{-# LANGUAGE BangPatterns, FlexibleContexts #-}

module Phonetic.Languages.Simplified.DataG where

import qualified Data.Foldable as F
import Data.Monoid
import Data.SubG
import Data.MinMax.Preconditions

data Result t a b c = R {line :: !(t a), propertiesF :: !b,  transPropertiesF :: !c} deriving Eq

instance (Ord (t a), Ord b, Ord c) => Ord (Result t a b c) where
  compare x y
    = case compare (transPropertiesF x) (transPropertiesF y) of
       !EQ -> case compare (propertiesF x) (propertiesF y) of
              !EQ -> compare (line x) (line y)
              !z -> z
       !z0 -> z0

data FuncRep2 a b c = D (a -> b) (b -> c)

getAC :: FuncRep2 a b c -> (a -> c)
getAC (D f g) = g . f

getAB :: FuncRep2 a b c -> (a -> b)
getAB (D f _) = f

getBC :: FuncRep2 a b c -> (b -> c)
getBC (D _ g) = g

maximumEl
  :: (Foldable t2, Ord c) => FuncRep2 (t a) b c
  -> t2 (t a)
  -> Result t a b c
maximumEl !frep2 data0 =
  let !l = F.maximumBy (\x y -> compare (getAC frep2 x) (getAC frep2 y)) data0
      !m = getAB frep2 l
      !tm = getBC frep2 m in R {line = l, propertiesF = m, transPropertiesF = tm}

minMaximumEls
  :: (InsertLeft t2 (t a), Monoid (t2 (t a)), Ord (t a), Ord c) => FuncRep2 (t a) b c
  -> t2 (t a)
  -> (Result t a b c,Result t a b c)
minMaximumEls !frep2 data0 =
  let (!ln,!lx) = minMax11ByC (\x y -> compare (getAC frep2 x) (getAC frep2 y)) data0
      !mn = getAB frep2 ln
      !mx = getAB frep2 lx
      !tmn = getBC frep2 mn
      !tmx = getBC frep2 mx in (R {line = ln, propertiesF = mn, transPropertiesF = tmn}, R {line = lx, propertiesF = mx, transPropertiesF = tmx})

maximumElR
  :: (Foldable t2, Ord c) => t2 (Result t a b c)
  -> Result t a b c
maximumElR = F.maximumBy (\x y -> compare (transPropertiesF x) (transPropertiesF y))

minMaximumElRs
  :: (InsertLeft t2 (Result t a b c), Monoid (t2 (Result t a b c)), Ord (t a), Ord b, Ord c) => t2 (Result t a b c)
  -> (Result t a b c,Result t a b c)
minMaximumElRs = minMax11ByC (\x y -> compare (transPropertiesF x) (transPropertiesF y))

-----------------------------------------------------------------------------------

-- | The second argument must be not empty for the function to work correctly.
innerPartitioning
  :: (InsertLeft t2 (t a), Monoid (t2 (t a)), InsertLeft t2 c, Monoid (t2 c), Ord c) => FuncRep2 (t a) b c
  -> t2 (t a)
  -> (t2 (t a), t2 (t a))
innerPartitioning !frep2 data0 =
  let !l = F.maximum . mapG (toTransPropertiesF' frep2) $ data0 in partitionG ((== l) . getAC frep2) data0

-- | The second argument must be not empty for the function to work correctly.
innerPartitioningR
  :: (InsertLeft t2 (Result t a b c), Monoid (t2 (Result t a b c)), InsertLeft t2 c, Monoid (t2 c), Ord c) => t2 (Result t a b c)
  -> (t2 (Result t a b c), t2 (Result t a b c))
innerPartitioningR dataR =
  let !l = F.maximum . mapG transPropertiesF $ dataR in partitionG ((== l) . transPropertiesF) dataR

maximumGroupsClassification
  :: (InsertLeft t2 (t a), Monoid (t2 (t a)), Ord c, InsertLeft t2 c, Monoid (t2 c), Integral d) => d
  -> FuncRep2 (t a) b c
  -> (t2 (t a), t2 (t a))
  -> (t2 (t a), t2 (t a))
maximumGroupsClassification !nGroups !frep2 (dataT,dataF)
 | F.null dataF = (dataT,mempty)
 | nGroups <= 0 = (dataT,dataF)
 | otherwise = maximumGroupsClassification (nGroups - 1) frep2 (dataT `mappend` partT,partF)
     where (!partT,!partF) = innerPartitioning frep2 dataF

maximumGroupsClassification1
  :: (InsertLeft t2 (t a), Monoid (t2 (t a)), Ord c, InsertLeft t2 c, Monoid (t2 c), Integral d) => d
  -> FuncRep2 (t a) b c
  -> t2 (t a)
  -> (t2 (t a), t2 (t a))
maximumGroupsClassification1 !nGroups !frep2 data0
 | F.null data0 = (mempty,mempty)
 | nGroups <= 0 = innerPartitioning frep2 data0
 | otherwise = maximumGroupsClassification (nGroups - 1) frep2 . innerPartitioning frep2 $ data0

maximumGroupsClassificationR2
  :: (InsertLeft t2 (Result t a b c), Monoid (t2 (Result t a b c)), Ord c, InsertLeft t2 c, Monoid (t2 c), Integral d) => d
  -> (t2 (Result t a b c), t2 (Result t a b c))
  -> (t2 (Result t a b c), t2 (Result t a b c))
maximumGroupsClassificationR2 !nGroups (dataT,dataF)
 | F.null dataF = (dataT,mempty)
 | nGroups <= 0 = (dataT,dataF)
 | otherwise = maximumGroupsClassificationR2 (nGroups - 1) (dataT `mappend` partT,partF)
     where (!partT,!partF) = innerPartitioningR dataF

maximumGroupsClassificationR
  :: (InsertLeft t2 (Result t a b c), Monoid (t2 (Result t a b c)), InsertLeft t2 c, Monoid (t2 c), Ord c, Integral d) => d
  -> t2 (Result t a b c)
  -> (t2 (Result t a b c), t2 (Result t a b c))
maximumGroupsClassificationR !nGroups dataR
 | F.null dataR = (mempty,mempty)
 | nGroups <= 0 = innerPartitioningR dataR
 | otherwise = maximumGroupsClassificationR2 (nGroups - 1) . innerPartitioningR $ dataR

toResultR
  :: FuncRep2 (t a) b c
  -> t a
  -> Result t a b c
toResultR !frep2 !ys = R { line = ys, propertiesF = m, transPropertiesF = tm}
  where !m = getAB frep2 ys
        !tm = getBC frep2 m

toPropertiesF'
  :: FuncRep2 (t a) b c
  -> t a
  -> b
toPropertiesF' !frep2 !ys = getAB frep2 ys

toTransPropertiesF'
  :: FuncRep2 (t a) b c
  -> t a
  -> c
toTransPropertiesF' !frep2 !ys = getAC frep2 ys
