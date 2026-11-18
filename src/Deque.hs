{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--no-termination" @-}
-- Double-ended queues i.e. deques
--
module Deque where

--import Language.Haskell.Liquid.ProofCombinators

-- invariant: both front and rear have to be non-empty whenever the deque contains at least two elements

{-@ data Deque a = Deque {fr :: [a], bk :: [a]} @-}
data Deque a = Deque [a] [a] -- pair of front and back
  deriving Show

empty :: Deque a
empty = Deque [] []

{-@ reflect isEmpty @-}
{-@ isEmpty :: dq:Deque a -> {v:Bool | v <=> (len (fr dq) == 0 && len (bk dq) == 0)} @-}
isEmpty :: Deque a -> Bool
isEmpty (Deque [] []) = True
isEmpty _             = False


-- push to the front and back;
-- these are worst-case O(1)
pushFront :: a -> Deque a -> Deque a
pushFront x (Deque fr bk) = Deque (x:fr) bk

pushBack :: a -> Deque a -> Deque a
pushBack x (Deque fr bk) = Deque fr (x:bk)

-- pop from the front or the back
{-@ popFront :: dq:{Deque a | len (bk dq) > 0} -> Deque a @-}
popFront :: Deque a -> Deque a
popFront dq = extract (normalize dq)
  where
    extract (Deque (x:fr) bk) = Deque fr bk
    extract (Deque [] [x]) = empty   -- special case for a single element
    -- extract _              = error "popFront: empty deque"

{-@ popBack :: dq:{Deque a | len (bk dq) > 0} -> Deque a @-}
popBack :: Deque a -> Deque a
popBack dq = extract (normalize dq)
  where
    extract (Deque fr (x:bk)) = Deque fr bk
    -- extract _                   = error "popBack: empty deque"

-- extract the front and back elements
{-@ front :: dq:{Deque a | len (bk dq) > 0} -> a @-}
front :: Deque a -> a
front dq = extract (normalize dq)
  where
    extract (Deque (x:_) _) = x
    extract (Deque [] [x])  = x
    -- extract _               = error "front: empty deque"  

{-@ back :: dq:{Deque a | len (bk dq) > 0} -> a @-}
back :: Deque a -> a
back dq = extract (normalize dq)
  where
    extract (Deque _ (x:_))   = x
    -- extract _                 = error "back: empty deque"


-- | normalize a deque
--{-@ reflect normalize @-}
normalize :: Deque a -> Deque a
normalize (Deque [] back) = Deque front' (reverse back')
  -- front is empty
  where
    n = length back
    k = div n 2
    (front', back') = splitAt k (reverse back)
normalize (Deque front []) = Deque front' (reverse back')
  -- back is empty
  where
    n = length front
    k = div n 2
    (front', back') = splitAt k front
-- all other cases: no change
normalize dq = dq



----------------------------------------------------
-- Testing amortized complexity bounds
----------------------------------------------------

  
-- cost functions
{-{-@ reflect normalizeT @-}
{-@ normalizeT :: Deque a -> {x:Int | x >= 1} @-}
normalizeT :: Deque a -> Int
normalizeT (Deque []  back)  = 1 + length back
normalizeT (Deque front [])  = 1 + length front
normalizeT _                  = 1

{-@ reflect popFrontT @-}
{-@ popFrontT :: Deque a -> {x:Int | x >= 1} @-}
popFrontT :: Deque a -> Int
popFrontT dq = 1 + normalizeT dq

{-@ reflect popBackT @-}
{-@ popBackT :: Deque a -> {x:Int | x >= 1} @-}
popBackT :: Deque a -> Int
popBackT dq = 1 + normalizeT dq

-- potential function
{-@ reflect phi @-}
{-@ phi :: Deque a -> {x:Int | x >= 0} @-}
phi :: Deque a -> Int
phi (Deque fr bk) = abs (length fr - length bk)


-------------------------------------------------------
-- Proof checking
-------------------------------------------------------

{-@ automatic-instances popFrontP @-}
{-@ popFrontP :: {dq:Deque a | not (isEmpty dq)} -> {popFrontT dq + phi (popFront dq) - phi dq <= 4} @-}
popFrontP :: Deque a -> Proof
popFrontP dq = trivial

{-@ automatic-instances popBackP @-}
{-@ popBackP :: {dq:Deque a | not (isEmpty dq)} -> {popBackT dq + phi (popBack dq) - phi dq <= 3} @-}
popBackP :: Deque a -> Proof
popBackP dq = trivial -}



