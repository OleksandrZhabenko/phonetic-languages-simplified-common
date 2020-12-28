-- |
-- Module      :  Phonetic.Languages.Simplified.StrictVG
-- Copyright   :  (c) OleksandrZhabenko 2020
-- License     :  MIT
-- Stability   :  Experimental
-- Maintainer  :  olexandr543@yahoo.com
--
-- Simplified version of the @phonetic-languages-common@ package.

{-# LANGUAGE BangPatterns #-}

module Phonetic.Languages.Simplified.StrictVG (
  -- * Working with vectors
  uniquenessVariants2GNB
  , uniquenessVariants2GNPB
  -- * Working with lists
  , uniquenessVariants2GNBL
  , uniquenessVariants2GNPBL
) where

import Phonetic.Languages.Permutations
import qualified Data.Vector as VB
import Phonetic.Languages.Simplified.DataG
import qualified Data.Foldable as F
import Data.SubG
import Data.SubG.InstancesPlus ()
import Data.Monoid

uniquenessVariants2GNB ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a))) => a -- ^ The first most common element in the \"whitespace symbols\" structure
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The permutations of 'Int' indices starting from 0 and up to n (n is probably less than 8).
  -> t (t a) -- ^ Must be obtained as 'subG' @whspss xs@
  -> VB.Vector (t a)
uniquenessVariants2GNB !hd f1 f2 f3 perms !subs = uniquenessVariants2GNPB mempty mempty hd f1 f2 f3 perms subs
{-# INLINE uniquenessVariants2GNB #-}

uniquenessVariants2GNPB ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a))) => t a
  -> t a
  ->  a -- ^ The first most common element in the whitespace symbols structure
  -> (t a -> VB.Vector a) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of @a@ so that the function can process further the permutations
  -> ((t (t a)) -> VB.Vector (VB.Vector a)) -- ^ The function that is used internally to convert to the boxed 'VB.Vector' of 'VB.Vector' of @a@ so that the function can process further
  -> (VB.Vector a -> t a) -- ^ The function that is used internally to convert from the boxed 'VB.Vector' of @a@ so that the function can process further
  -> VB.Vector (VB.Vector Int) -- ^ The permutations of 'Int' indices starting from 0 and up to n (n is probably less than 7).
  -> t (t a) -- ^ Must be obtained as @subG whspss xs@
  -> VB.Vector (t a)
uniquenessVariants2GNPB !ts !us !hd f1 f2 f3 perms !subs
  | F.null subs = mempty
  | otherwise =
     let !uss = (hd %@ us) %^ mempty
         !baseV = VB.map (hd %@) . f2 $ subs
         !ns = universalSetG ts uss f1 f2 perms baseV in VB.map f3 ns

uniquenessVariants2GNBL ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a))) => a -- ^ The first most common element in the \"whitespace symbols\" structure
  -> (t a -> [a]) -- ^ The function that is used internally to convert to the @[a]@ so that the function can process further the permutations
  -> ((t (t a)) -> [[a]]) -- ^ The function that is used internally to convert to the @[[a]]@ so that the function can process further
  -> ([a] -> t a) -- ^ The function that is used internally to convert to the needed representation so that the function can process further
  -> [VB.Vector Int] -- ^ The permutations of 'Int' indices starting from 0 and up to n (n is probably less than 8).
  -> t (t a) -- ^ Must be obtained as 'subG' @whspss xs@
  -> [t a]
uniquenessVariants2GNBL !hd f1 f2 f3 perms !subs = uniquenessVariants2GNPBL mempty mempty hd f1 f2 f3 perms subs
{-# INLINE uniquenessVariants2GNBL #-}

uniquenessVariants2GNPBL ::
  (Eq a, Foldable t, InsertLeft t a, Monoid (t a), Monoid (t (t a))) => t a
  -> t a
  ->  a -- ^ The first most common element in the whitespace symbols structure
  -> (t a -> [a]) -- ^ The function that is used internally to convert to the @[a]@ so that the function can process further the permutations
  -> ((t (t a)) -> [[a]]) -- ^ The function that is used internally to convert to the @[[a]]@ so that the function can process further
  -> ([a] -> t a) -- ^ The function that is used internally to convert to the needed representation that the function can process further
  -> [VB.Vector Int] -- ^ The permutations of 'Int' indices starting from 0 and up to n (n is probably less than 7).
  -> t (t a) -- ^ Must be obtained as @subG whspss xs@
  -> [t a]
uniquenessVariants2GNPBL !ts !us !hd f1 f2 f3 perms !subs
  | F.null subs = mempty
  | otherwise =
     let !uss = (hd %@ us) %^ mempty
         !baseV = VB.fromList . map (hd %@) . f2 $ subs
         !ns = universalSetGL ts uss f1 f2 perms baseV in map f3 ns

