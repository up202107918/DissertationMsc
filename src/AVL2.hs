{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--no-termination" @-}

module AVL2 where

import Prelude hiding (max)
import qualified Data.Set as S 

-- | Trees with value less than X
{-@ type AVLL a X = AVL {v:a | v < X}  @-}

-- | Trees with value greater than X
{-@ type AVLR a X = AVL {v:a | v > X}  @-}

{-@ measure realHeight @-}
{-@ realHeight :: AVL a -> Nat @-}
realHeight                :: AVL a -> Int
realHeight Leaf           = 0
realHeight (Node _ l r _) = nodeHeight l r

{-@ inline nodeHeight @-}
{-@ nodeHeight :: AVL a -> AVL a -> {x:Nat | x >= 1} @-}
nodeHeight :: AVL a -> AVL a -> Int
nodeHeight l r = 1 + max hl hr
  where
    hl         = realHeight l
    hr         = realHeight r

{-@ inline max @-}
{-@ max :: x:Nat -> y:Nat -> {v:Nat | v >= x && v >= y} @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

{-@ inline isLeaf @-}
isLeaf :: AVL a -> Bool
isLeaf Leaf = True
isLeaf _    = False

{-@ inline isReal @-}
{-@ isReal :: v:Nat -> l:AVL a -> r:AVL a -> Bool @-}
isReal v l r = v == nodeHeight l r

{-@ inline isBal @-}
{-@ isBal :: l:AVL a -> r:AVL a -> n:Nat -> Bool @-}
isBal l r n = 0 - n <= d && d <= n
  where
    d = realHeight l - realHeight r

{-@ data AVL a = Leaf
               | Node { key :: a
                      , l   :: AVLL a key
                      , r   :: {v:AVLR a key | isBal l v 1}
                      , ah :: {v:Nat | isReal v l r}
                      }                                  @-}
data AVL a =
    Leaf
  | Node { key :: a      -- value
         , l   :: AVL a  -- left subtree
         , r   :: AVL a  -- right subtree
         , ah  :: Int    -- height
         }
    deriving (Show)

-- | Trees of height N
{-@ type AVLN a N = {v: AVL a | realHeight v = N} @-}

-- | Trees of height equal to that of another T
{-@ type AVLT a T = AVLN a {realHeight T} @-}

{-@ empty :: AVLN a 0 @-}
empty :: AVL a
empty = Leaf

{-@ singleton :: a -> AVLN a 1 @-}
singleton :: a -> AVL a
singleton x = Node x empty empty 1

{-@ node :: x:a -> l:AVLL a x -> r:{AVLR a x | isBal l r 1}
           -> AVLN a {nodeHeight l r}
  @-}
node :: a -> AVL a -> AVL a -> AVL a
node v l r = Node v l r h
 where
   h       = 1 + max hl hr
   hl      = getHeight l
   hr      = getHeight r

{-@ inline leftBig @-}
--{-@ leftBig :: l:AVL a -> r:AVL a -> Bool @-}
leftBig :: AVL a -> AVL a -> Bool
leftBig l r = diff l r == 2

{-@ inline rightBig @-}
--{-@ rightBig :: l:AVL a -> r:AVL a -> Bool @-}
rightBig :: AVL a -> AVL a -> Bool
rightBig l r = diff r l == 2

{-@ inline diff @-}
--{-@ diff :: s:AVL a -> t:AVL a -> Int @-}
diff :: AVL a -> AVL a -> Int
diff s t = getHeight s - getHeight t

{-@ measure getHeight @-}
{-@ getHeight :: AVL a -> Nat @-}
getHeight :: AVL a -> Int
getHeight Leaf           = 0
getHeight (Node _ _ _ n) = n

{-@ measure balFac @-}
balFac :: AVL a -> Int
balFac Leaf           = 0
balFac (Node _ l r _) = getHeight l - getHeight r
--balFac (Node _ l r _) = diff l r
--balFac (Node _ l r _) = realHeight l - realHeight r

{-@ inline leftHeavy @-}
--{-@ leftHeavy :: t:AVL a -> Bool @-}
leftHeavy :: AVL a -> Bool 
leftHeavy  t = balFac t > 0

{-@ inline rightHeavy @-}
--{-@ rightHeavy :: t:AVL a -> Bool @-}
rightHeavy :: AVL a -> Bool 
rightHeavy t = balFac t < 0

{-@ inline noHeavy @-}
--{-@ noHeavy :: t:AVL a -> Bool @-}
noHeavy :: AVL a -> Bool
noHeavy t = balFac t == 0

{-
{-@ balL0 :: x:a
          -> l:{AVLL a x | noHeavy l && not (isLeaf l)} 
          -> r:{AVLR a x | leftBig l r}
          -> AVLN a {1 + realHeight l}
  @-}
balL0 :: a -> AVL a -> AVL a -> AVL a
balL0 v (Node lv ll lr _) r = node lv ll (node v lr r)
-}
{-
{-@ balLL :: x:a
          -> l:{AVLL a x | leftHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLT a l
  @-}
balLL v (Node lv ll lr _) r = node lv ll (node v lr r)

{-@ balLR :: x:a
          -> l:{AVLL a x | rightHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLT a l
  @-}
balLR v (Node lv ll (Node lrv lrl lrr _) _) r
  = node lrv (node lv ll lrl) (node v lrr r)
-}
{-
{-@ balR0 :: x:a
          -> l: AVLL a x
          -> r: {AVLR a x | rightBig l r && noHeavy r}
          -> AVLN a {realHeight r + 1}
  @-}
balR0 v (Node rv rl rr _) r = node rv (node v rl r) rr

{-@ balRR :: x:a
          -> l: AVLL a x
          -> r:{AVLR a x | rightBig l r && rightHeavy r}
          -> AVLT a r
  @-}
balRR v l (Node rv rl rr _) = node rv (node v l rl) rr
{-@ balRL :: x:a
          -> l: AVLL a x
          -> r:{AVLR a x | rightBig l r && leftHeavy r}
          -> AVLT a r
  @-}
balRL v l (Node rv rl rr _) = node rv (node v l rl) rr
-}
{-@ inline eqOrUp @-}
eqOrUp s t = d == 0 || d == 1
  where
    d      = diff t s

{-
{-@ insL :: x:a
         -> t:{AVL a | x < key t && 0 < realHeight t}
         -> {v: AVL a | eqOrUp t v}
  @-}
insL a (Node v l r _)
  | isLeftBig && leftHeavy l'  = balLL v l' r
  | isLeftBig && rightHeavy l' = balLR v l' r
  | isLeftBig                  = balL0 v l' r
  | otherwise                  = node  v l' r
  where
    isLeftBig                  = leftBig l' r
    l'                         = insert a l

{-@ insR :: x:a
         -> t:{AVL a  | key t < x && 0 < realHeight t }
         -> {v: AVL a | eqOrUp t v}
  @-}
insR = undefined

{-@ bal :: x:a
        -> l:AVLL a x
        -> r:{AVLR a x | isBal l r 2}
        -> {t:AVL a | reBal l r t}
  @-}
bal v l r
  | isLeftBig  && leftHeavy l  = balLL v l r
  | isLeftBig  && rightHeavy l = balLR v l r
  | isLeftBig                  = balL0 v l r
  | isRightBig && leftHeavy r  = balRL v l r
  | isRightBig && rightHeavy r = balRR v l r
  | isRightBig                 = balR0 v l r
  | otherwise                  = node  v l r
  where
    isLeftBig                  = leftBig l r
    isRightBig                 = rightBig l r

{-@ inline reBal @-}
reBal l r t = bigHt l r t && balHt l r t

{-@ inline balHt @-}
balHt l r t = not (isBal l r 1) || isReal (realHeight t) l r

{-@ inline bigHt @-}
bigHt l r t = lBig && rBig
  where
    lBig    = not (hl >= hr) || (eqOrUp l t)
    rBig    = (hl >= hr)     || (eqOrUp r t)
    hl      = realHeight l
    hr      = realHeight r

{-@ insert' :: a -> s:AVL a -> {t: AVL a | eqOrUp s t} @-}
insert' a t@(Node v l r n)
  | a < v      = bal v (insert' a l) r
  | a > v      = bal v l (insert' a r)
  | otherwise  = t
insert' a Leaf = singleton a

{-@ delete    :: a -> s:AVL a -> {t:AVL a | eqOrDn s t} @-}
delete y (Node x l r _)
  | y < x     = bal x (delete y l) r
  | x < y     = bal x l (delete y r)
  | otherwise = merge x l r
delete _ Leaf = Leaf

{-@ inline eqOrDn @-}
eqOrDn s t = eqOrUp t s

{-@ merge :: x:a -> l:AVLL a x -> r:{AVLR a x | isBal l r 1}
          -> {t:AVL a | bigHt l r t}
  @-}
merge _ Leaf r = r
merge _ l Leaf = l
merge x l r    = bal y l r'
  where
   (y, r')     = getMin r

getMin (Node x Leaf r _) = (x, r)
getMin (Node x l r _)    = (x', bal x l' r)
  where
    (x', l')             = getMin l
-}
{-@ measure elems @-}
elems                :: (Ord a) => AVL a -> S.Set a
elems (Node x l r _) = (S.singleton x) `S.union`
                       (elems l)       `S.union`
                       (elems r)
elems Leaf           = S.empty
{-
-- FIXME https://github.com/ucsd-progsys/liquidhaskell/issues/332
{-@ member :: (Ord a) => x:a -> t:AVL a -> {v: Bool | v <=> hasElem x t} @-}
member x t = undefined
-}
{-@ type BoolP P = {v:Bool | v <=> P} @-}

{-@ inline hasElem @-}
hasElem x t = S.member x (elems t)

{-}
{-@ insertAPI :: (Ord a) => a -> s:AVL a -> {t:AVL a | addElem x s t} @-}
insertAPI x s = insert' x s
-}

{-@ inline addElem @-}
addElem       :: Ord a => a -> AVL a -> AVL a -> Bool
addElem x s t = (elems t) == (elems s) `S.union` (S.singleton x)

{-
{-@ deleteAPI :: (Ord a) => a -> s:AVL a -> {t: AVL a | delElem x s t} @-}
deleteAPI x s = delete x s
-}

{-@ inline delElem @-}
delElem       :: Ord a => a -> AVL a -> AVL a -> Bool
delElem x s t = (elems t) == (elems s) `S.difference` (S.singleton x)