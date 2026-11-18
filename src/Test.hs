{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--no-termination" @-}

module Test where

{-@ inline foo @-}
foo :: Int -> Int
foo x = x + 1

{-@ inline bar @-}
bar :: Int -> Bool
bar x = foo x == 1

{-@ mo :: x:Int -> { bar x == bar x } @-}
mo :: Int -> ()
mo _ = ()
