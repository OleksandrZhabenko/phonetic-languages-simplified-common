-- |
-- Module      :  Phonetic.Languages.Simplified.Lists.UniquenessPeriodsG
-- Copyright   :  (c) OleksandrZhabenko 2020
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  olexandr543@yahoo.com
--
-- Generalization of the uniqueness-periods and uniqueness-periods-general
-- packages functionality.
--

{-# LANGUAGE BangPatterns #-}

module Phonetic.Languages.Simplified.Lists.UniquenessPeriodsG (
  -- * Vector functions
  diverse2G
  -- * List functions
  , diverse2GL
)where

import GHC.Int
import qualified Data.Vector as VB
import Data.List
import Data.Maybe (mapMaybe)


-- | A vectors simplified variant of the diverse2 metrics from the @phonetic-languages-properties@ package.
diverse2G whspss v
 | VB.null v = 0
 | otherwise = VB.sum . VB.mapMaybe (helpG sum whspss) . VB.unfoldr f . VB.map (\(j,t) -> (toEnum j,t)) $ v1
     where !v1 = VB.indexed v
           !vs = VB.toList . VB.map toEnum . VB.findIndices (`elem` whspss) $ v
           f !x = if VB.null x then Nothing else let !idX0 = snd . VB.unsafeIndex x $ 0 in Just . (\vws (v2,v3) -> ((helpUPV3 vws [] . VB.toList .
                    VB.map fst $ v2,snd . VB.unsafeIndex v2 $ 0),v3)) vs . VB.partition (\(_,xs) -> xs == idX0) $ x

-- | A lists variant of the diverse2 metrics from the @phonetic-languages-properties@ package.
diverse2GL whspss ws
 | null ws = 0
 | otherwise = sum . mapMaybe (helpG sum whspss) . unfoldr f $ ks
     where !ks = indexedL '\00' ws
           !vs = mapMaybe g ks
           g x
            | (`elem` whspss) . snd $ x = Just (fst x)
            | otherwise = Nothing
           {-# INLINE g #-}
           f !x = if null x then Nothing else let !idX0 = snd . head $ x in Just . (\vws (v2,v3) -> ((helpUPV3 vws [] .
                    map fst $ v2,snd . head $ v2),v3)) vs . partition (\(_,xs) -> xs == idX0) $ x

-- | The first and the third list arguments of numbers (if not empty) must be sorted in the ascending order.
helpUPV3 :: [Int16] -> [Int16] -> [Int16] -> [Int16]
helpUPV3 (z:zs) !acc (x:y:xs)
 | compare ((x - z) * (y - z)) 0 == LT = helpUPV3 zs ((y - x):acc) (y:xs)
 | compare y z == GT = helpUPV3 zs acc (x:y:xs)
 | otherwise = helpUPV3 (z:zs) acc (y:xs)
helpUPV3 _ !acc _ = acc

indexedL :: Foldable t => b -> t b -> [(Int16, b)]
indexedL y = foldr f v
  where v = [(1::Int16,y)]
        f x ((j,z):ys) = (j-1,x):(j,z):ys

helpG :: (Eq a) => ([b] -> b) -> [a] -> ([b], a) -> Maybe b
helpG h xs (ts, x)
  | null ts = Nothing
  | x `elem` xs = Nothing
  | otherwise = Just (h ts)
{-# INLINE helpG #-}
