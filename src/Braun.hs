{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
--{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}

module Braun where 

import Language.Haskell.Liquid.ProofCombinators

{-@ inline notZero @-}
notZero :: Int -> Bool
notZero x = x /= 0 

{-@ saveDiv :: Int -> d:{Int | notZero d} -> Int @-}
saveDiv :: Int -> Int -> Int
saveDiv x y = div x y

{-@ measure allEven @-}
allEven :: [Int] -> Bool
allEven [] = True
allEven (x:xs) = even x && allEven xs

{-@ type EvenList = {xs : [Int] | allEven xs} @-}

{-@ lstEvens :: xs : EvenList @-}
lstEvens :: [Int]
lstEvens = [2,4,6,8]

{-{-@ ple lstEvens_prf @-}
{-@ lstEvens_prf :: {allEven [2,4,6,8] == True} @-}
lstEvens_prf :: Proof
lstEvens_prf = allEven [2,4,6,8]
    === (even 2 && allEven [4,6,8])
    === (even 4 && allEven [6,8])
    === (even 6 && allEven [8])
    === (even 8 && allEven [])
    *** QED
-}

data Tree a = Node a (Tree a) (Tree a) | Nil

{- 
{-@ measure balanced @ -}
{-@ balanced :: Tree a -> Bool @ -}
balanced Nil = True
balanced t@( Node _ l r) = balanced l && balanced r && h t - mh t <= 1

{-@ measure h @ -}
{-@ h :: t: Tree a -> i : { Nat | i >= mh t } @ -}
h :: Tree a -> Int
h Nil = 0
h (Node _ l r) = 1 + max (h l) (h r)

{-@ measure mh @ -}
{-@ mh :: t : Tree a -> i : { Nat | i <= h t } @ -}
mh :: Tree a -> Int
mh Nil = 0
mh (Node _ l r) = 1 + min (mh l) (mh r)

{-@ type BTree a = { t: Tree a | balanced t } @ -}

{-@ prop_2 :: t : BTree a -> { log2F (nc t + 1) == mh t } @ -}
prop_2 t = log2F (nc t + 1) == mh t ?
(( nc t + 1 >= pow2 (mh t) ? prop_4 t) *** QED )
&&&
(nc t + 1 < pow2 (mh t + 1) ? prop_3 t *** QED ))
? prop_5 (mh t) (nc t + 1) *** QED

{-@ prop_1 :: t : BTree a -> { log2C (nc t + 1) == h t } @ -}
prop_1 Nil = ()
prop_1 t | h t == mh t = log2C n == h t ? prop_6 t
=== log2F (nc t + 1) == h t ? prop_2 t
=== mh t == h t *** QED
| h t == mh t + 1 = log2C n == h t ? prop_7 t
=== log2F (nc t + 1) + 1 == h t ? prop_2 t
=== mh t + 1 == h t *** QED

-}