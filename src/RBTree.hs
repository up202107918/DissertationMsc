{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
--{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-termination" @-}

module RBTree where 

import Prelude hiding (insert)

data Color = Red | Black
    deriving (Show,Eq)

{-@ data RBTree a = Empty | Tree { color :: Color, left :: RBTree a, value :: a, right :: RBTree a } @-}
data RBTree a = Empty | Tree Color (RBTree a) a (RBTree a)
    deriving (Show,Eq)

{-@ type weakRBT a = {v:RBTree a | isWeak v} @-}

{-@ member :: Ord a => a -> RBTree a -> Bool @-}
member :: Ord a => a -> RBTree a -> Bool
member _ Empty = False
member x (Tree _ left y right)
  | x < y     = member x left
  | x > y     = member x right
  | otherwise = True

{-
balance :: Ord a => Color -> RBTree a -> a -> RBTree a -> RBTree a 
balance Black (Tree Red (Tree Red a x b) y c) z d = Tree Red (Tree Black a x b) y (Tree Black c z d)
balance Black (Tree Red a x (Tree Red b y c)) z d = Tree Red (Tree Black a x b) y (Tree Black c z d)
balance Black a x (Tree Red (Tree Red b y c) z d) = Tree Red (Tree Black a x b) y (Tree Black c z d)
balance Black a x (Tree Red b y (Tree Red c z d)) = Tree Red (Tree Black a x b) y (Tree Black c z d)
balance color left val right = Tree color left val right
-}

{-@ insert :: (Ord a) => a -> RBTree a -> RBTree a @-}
insert :: Ord a => a -> RBTree a -> RBTree a
{-insert x s = Tree Black a y b
  where
    ins Empty = Tree Red Empty x Empty
    ins s@(Tree color a y b)
      | x < y     = balance color (ins a) y b
      | x > y     = balance color a y (ins b)
      | otherwise = s
    Tree _ a y b = ins s
-}
insert x s 

{-@ ins :: (Ord a) => a -> t:RBTree a -> v:{weakRBT a | (getColor t /= Red => redInvariant v) && 
    getBlackHeight v == getBlackHeight t} @-}
ins :: Ord a => a -> RBTree a -> RBTree a
--ins x Empty = Tree Red Empty x Empty
ins x (Tree color a y b)
  | x < y     = balanceL color (ins x a) y b
  | x > y     = balanceR color a y (ins x b)

{-@ balanceL :: (Ord a) => color:Color -> left:{weakRBT a | color == Red => redInvariant left} -> a 
  -> right:{RBTree a | getBlackHeight right == getBlackHeight left} -> v:{weakRBT a | (color /= Red => redInvariant v) &&
    getBlackHeight v == (if color == Black then 1 else 0) + getBlackHeight left} @-}
balanceL :: (Ord a) => Color -> RBTree a -> a -> RBTree a -> RBTree a
balanceL Black (Tree Red (Tree Red a x b) y c) z d = Tree Red (Tree Black a x b) y (Tree Black c z d)
balanceL Black (Tree Red a x (Tree Red b y c)) z d = Tree Red (Tree Black a x b) y (Tree Black c z d)
balanceL color left val right = Tree color left val right

{-@ balanceR :: (Ord a) => color:Color -> left:RBTree a -> a -> right:{weakRBT a | (color == Red => redInvariant right) &&
  getBlackHeight right == getBlackHeight left} -> v:{weakRBT a | (color /= Red => redInvariant v) && 
  getBlackHeight v == (if color == Black then 1 else 0) + getBlackHeight left} @-}
balanceR :: (Ord a) => Color -> RBTree a -> a -> RBTree a -> RBTree a
balanceR Black a x (Tree Red (Tree Red b y c) z d) = Tree Red (Tree Black a x b) y (Tree Black c z d)
balanceR Black a x (Tree Red b y (Tree Red c z d)) = Tree Red (Tree Black a x b) y (Tree Black c z d)
balanceR color left val right = Tree color left val right

isNotRedViolation :: Color -> RBTree a -> RBTree a -> Bool
isNotRedViolation Red (Tree Red _ _ _) _ = False
isNotRedViolation Red _ (Tree Red _ _ _) = False
isNotRedViolation _ _ _ = True

{-@ measure getColor @-}
getColor :: RBTree a -> Color
getColor (Tree color _ _ _) = color
getColor Empty = Black

{-@ measure getLeft @-}
getLeft :: RBTree a -> RBTree a
getLeft Empty = Empty
getLeft (Tree _ left _ _) = left

{-@ measure getRight @-}
getRight :: RBTree a -> RBTree a
getRight Empty = Empty
getRight (Tree _ _ _ right) = right

{-@ measure getBlackHeight @-}
getBlackHeight :: RBTree a -> Int
getBlackHeight Empty = 1
getBlackHeight (Tree color left _ right) =
  (if color == Black then 1 else 0) + getBlackHeight left

{-@ measure blackInvariant @-}
blackInvariant :: RBTree a -> Bool
blackInvariant Empty = True
blackInvariant (Tree color left _ right) = getBlackHeight left == getBlackHeight right
                                        && blackInvariant left
                                        && blackInvariant right

{-@ measure redInvariant @-}
redInvariant :: RBTree a -> Bool
redInvariant Empty = True
redInvariant (Tree color left _ right) = isNotRedViolation color left right
                                        && redInvariant left
                                        && redInvariant right

{-@ inline isRBT @-}
isRBT :: RBTree a -> Bool
isRBT t = redInvariant t && blackInvariant t

{-@ inline isWeak @-}
isWeak :: RBTree a -> Bool
isWeak t = blackInvariant t
          && redInvariant (getLeft t)
          && redInvariant (getRight t)

{-@ newRBT :: c:Color -> {l:RBTree a | c /= Red || getColor l /= Red} -> a 
 -> {r:RBTree a | (c /= Red || getColor r /= Red) && getBlackHeight r == getBlackHeight l} -> RBTree a @-}
newRBT :: Color -> RBTree a -> a -> RBTree a -> RBTree a
newRBT color left val right = Tree color left val right