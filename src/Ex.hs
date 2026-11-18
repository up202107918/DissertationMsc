{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--no-termination" @-}

module Ex where 
import Prelude hiding (max,floor)

{-@ inline max @-}
{-@ max :: Int -> Int -> Int @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

{-@ floor :: x:Int -> {v:Nat | v = max 0 x} @-}
floor :: Int -> Int
floor x 
  | x <= 0    = 0
  | otherwise = x