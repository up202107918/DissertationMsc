{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--no-termination" @-}

module BST where

{-@ data BST a    = Leaf
                  | Node { root  :: a
                         , left  :: BSTL a root
                         , right :: BSTR a root } @-}
data BST a = Leaf
           | Node { root  :: a
                  , left  :: BST a
                  , right :: BST a }
  deriving (Show)

{-@ type BSTL a X = BST {v:a | v < X}             @-}
{-@ type BSTR a X = BST {v:a | X < v}             @-}

mem                 :: (Ord a) => a -> BST a -> Bool
mem _ Leaf          = False
mem k (Node k' l r)
  | k == k'         = True
  | k <  k'         = mem k l
  | otherwise       = mem k r

one   :: a -> BST a
one x = Node x Leaf Leaf

add                  :: (Ord a) => a -> BST a -> BST a
add k' Leaf          = one k'
add k' t@(Node k l r)
  | k' < k           = Node k (add k' l) r
  | k  < k'          = Node k l (add k' r)
  | otherwise        = t

{-@ data MinPair a = MP { mElt :: a, rest :: BSTR a mElt} @-}
data MinPair a = MP { mElt :: a, rest :: BST a }
  deriving (Show)
