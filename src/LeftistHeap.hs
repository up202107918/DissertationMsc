{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}

module LeftistHeap where

data LeftistHeap a = Empty
                   | Tree Int a (LeftistHeap a) (LeftistHeap a)
  deriving Show

rank :: LeftistHeap a -> Int
rank Empty          = 0
rank (Tree r _ _ _) = r

empty :: LeftistHeap a
empty = Empty

isEmpty :: LeftistHeap a -> Bool
isEmpty Empty = True
isEmpty _     = False

insert :: Ord a => a -> LeftistHeap a -> LeftistHeap a
insert x h = merge (Tree 1 x Empty Empty) h

merge :: Ord a => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
merge h Empty = h
merge Empty h = h
merge h1@(Tree _ x a1 b1) h2@(Tree _ y a2 b2)
  | x <= y    = makeT x a1 (merge b1 h2)
  | otherwise = makeT y a2 (merge h1 b2)

makeT :: a -> LeftistHeap a -> LeftistHeap a -> LeftistHeap a
makeT x a b
  | rank a >= rank b = Tree (rank b + 1) x a b
  | otherwise        = Tree (rank a + 1) x b a

deleteMin :: Ord a => LeftistHeap a -> LeftistHeap a
deleteMin Empty = Empty
deleteMin (Tree _ _ a b) = merge a b

findMin :: Ord a => LeftistHeap a -> a
findMin Empty = error "Empty heap"
findMin (Tree _ x _ _) = x