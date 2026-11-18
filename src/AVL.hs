{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--no-termination" @-}
 
module AVL where

{-@ type AVLL a X = AVL {v:a | v < X} @-}
{-@ type AVLR a X = AVL {v:a | v > X} @-}

{-@ data AVL a = Empty 
            | Node {h :: Nat, key :: a, left :: AVLL a key, right :: AVLR a key} @-}
data AVL a = Empty 
            | Node Int a (AVL a) (AVL a) 
            deriving (Show, Eq)

{-@ measure height @-}
{-@ height :: AVL a -> Nat @-}
height :: AVL a -> Int
height (Node h _ _ _) = h
height Empty = 0

{-@ constructNode :: x:a -> left:AVL a -> right:AVL a -> {v:AVL a | height v >= 1} @-}
constructNode :: a -> AVL a -> AVL a -> AVL a
constructNode x left right = Node h x left right
  where h = 1 + max (height left) (height right)

{-@ deviation :: AVL a -> Nat @-}
deviation :: AVL a -> Int
deviation Empty = 0
deviation (Node _ _ left right) = height left - height right

search :: Ord a => a -> AVL a -> Bool
search x Empty = False
search x (Node _ y left right)
  | x == y = True
  | x < y  = search x left
  | x > y  = search x right

rotateRight :: AVL a -> AVL a
rotateRight (Node _ x (Node _ y t1 t2) t3) = constructNode y t1 (constructNode x t2 t3)
rotateRight t = t -- nada a fazer nos outros casos

rotateLeft :: AVL a -> AVL a
rotateLeft (Node _ x t1 (Node _ y t2 t3)) = constructNode y (constructNode x t1 t2) t3
rotateLeft t = t -- nada a fazer nos outros casos

correctRight :: AVL a -> AVL a
correctRight (Node _ x t1 t2)
  | deviation t1 == -1 = rotateRight (constructNode x (rotateLeft t1) t2)
  | otherwise = rotateRight (constructNode x t1 t2)
correctRight t = t -- nada a fazer noutros casos

correctLeft :: AVL a -> AVL a
correctLeft (Node _ x t1 t2)
  | deviation t2 == 1 = rotateLeft (constructNode x t1 (rotateRight t2))
  | otherwise = rotateLeft (constructNode x t1 t2)
correctLeft t = t -- nada a fazer noutros casos

balancing :: AVL a -> AVL a
balancing t
  | d == 2 = correctRight t
  | d == -2 = correctLeft t
  | otherwise = t
  where d = deviation t

insert :: Ord a => a -> AVL a -> AVL a
insert x Empty = Node 1 x Empty Empty
insert x (Node _ y left right)
  | x==y -- já ocorre
  = Node h1 y left right
  | x<y  -- inserir à esquerda
  = balancing (Node h2 y (insert x left) right)
  | x>y -- inserir à direita
  = balancing (Node h3 y left (insert x right))
  where h1 = 1 + max (height left) (height right)
        h2 = 1 + max (height (insert x left)) (height right)
        h3 = 1 + max (height left) (height (insert x right))

remove :: Ord a => a -> AVL a -> AVL a
remove x Empty = Empty
remove x (Node _ y left right)
  | x < y = balancing (constructNode y (remove x left) right)
  | x > y = balancing (constructNode y left (remove x right))
  | otherwise = case (left, right) of
      (Empty, Empty) -> Empty
      (Empty, _) -> right
      (_, Empty) -> left
      _ -> let (minRight, newRight) = removeMin right
           in balancing (constructNode minRight left newRight)

removeMin :: AVL a -> (a, AVL a)
removeMin (Node _ y Empty right) = (y, right)
removeMin (Node _ y left right) = let (minLeft, newLeft) = removeMin left
                                  in (minLeft, balancing (constructNode y newLeft right))
