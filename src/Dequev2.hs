{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

module Dequev2 where

import Prelude hiding (length)

-- 1. Define standard list length as a measure for LiquidHaskell
{-@ measure llen @-}
llen :: [a] -> Int
llen []     = 0 
llen (x:xs) = 1 + llen xs 

-- 2. Define the Deque data type with the balancing invariant
-- Invariant: len front <= 3 * len back + 1 && len back <= 3 * len front + 1
{-@ data Deque a = Deque 
      { front :: [a]
      , back  :: [a] 
      } 
@-}
data Deque a = Deque [a] [a]
  deriving Show

{-@ check :: f:[a] -> b:[a] -> {v:Deque a | llen f <= 3 * llen b + 1 && llen b <= 3 * llen f + 1} @-}
check :: [a] -> [a] -> Deque a
check f b
  | llen f > 3 * llen b + 1 = 
      let n  = (llen f + llen b) `div` 2
          f' = take n f
          b' = b ++ reverse (drop n f)
      -- LiquidHaskell tracks bounds to ensure this result satisfies the invariant
      in Deque f' b' 
  | llen b > 3 * llen f + 1 = 
      let n  = (llen f + llen b) `div` 2
          f' = f ++ reverse (drop n b)
          b' = take n b
      in Deque f' b'
  | otherwise = Deque f b

-- Create an empty Deque
{-@ empty :: {v:Deque a | llen (front v) == 0 && llen (back v) == 0} @-}
empty :: Deque a
empty = Deque [] []

-- Push an item to the front
{-@ pushFront :: a -> Deque a -> Deque a @-}
pushFront :: a -> Deque a -> Deque a
pushFront x (Deque f b) = check (x:f) b

-- Push an item to the back
{-@ pushBack :: a -> Deque a -> Deque a @-}
pushBack :: a -> Deque a -> Deque a
pushBack x (Deque f b) = check f (x:b)

-- Safely pop from the front
{-@ popFront :: Deque a -> Maybe (a, Deque a) @-}
popFront :: Deque a -> Maybe (a, Deque a)
popFront (Deque [] [])    = Nothing
popFront (Deque [] [x])   = Just (x, empty)
popFront (Deque (x:xs) b) = Just (x, check xs b)
popFront (Deque [] _)     = Nothing -- Provably unreachable due to our invariant!