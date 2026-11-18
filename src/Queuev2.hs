{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--no-termination" @-}

module Queuev2 where

{-@ type Nat = {x:Int | x >= 0} @-}

--
-- Purely functional queues a.k.a. "Batched queues"
-- O(1) amortized cost for all operations
--
--import Test.QuickCheck

newtype Queue a = MkQ ([a], [a]) -- pair of front and back
                deriving Show

-- front is in direct order
-- back is in reverse order
-- invariant: front is empty => back is also empty
-- use a newtype to allow custom instance declarations

empty :: Queue a
empty = MkQ ([], [])

isEmpty :: Queue a -> Bool
isEmpty (MkQ (fr, _)) = null fr

-- add to the back 
enqueue :: a -> Queue a -> Queue a
enqueue x (MkQ (fr,bk)) = makeQueue fr (x:bk)

-- front element
front :: Queue a -> a
front (MkQ (x:fr, bk)) = x
front _                = error "empty queue"

-- remove the front
dequeue :: Queue a -> Queue a
dequeue (MkQ (x:fr, bk)) = makeQueue fr bk
dequeue _                = error "empty queue"


-- smart constructor
makeQueue :: [a] -> [a] -> Queue a
makeQueue [] bk = MkQ (reverse bk, [])
makeQueue fr bk = MkQ (fr, bk)

-------------------------------------------------------
-- Testing amortized bounds
-------------------------------------------------------

{-instance Arbitrary a => Arbitrary (Queue a) where
  arbitrary = MkQ <$> arbitrary -}
    
-- actual cost functions
{-@ reflect enqueueT @-}
{-@ enqueueT :: a -> Queue a -> {x:Int | x >= 1} @-}
enqueueT :: a -> Queue a -> Int
enqueueT x (MkQ (fr,bk)) = makeQueueT fr (x:bk)

{-@ reflect dequeueT @-}
{-@ dequeueT :: Queue a -> {x:Int | x >= 1} @-}
dequeueT :: Queue a -> Int
dequeueT (MkQ (x:fr,bk)) = makeQueueT fr bk

{-@ reflect makeQueueT @-}
{-@ makeQueueT :: [a] -> [a] -> {x:Int | x >= 1} @-}
makeQueueT :: [a] -> [a] -> Int
makeQueueT [] bk = 1 + length bk
makeQueueT fr bk = 1

-- potential
{-@ reflect phi @-}
{-@ phi :: Queue a -> Nat @-}
phi :: Queue a -> Int
phi (MkQ (fr, bk)) = length bk


{-prop_InitialPotential :: Property
prop_InitialPotential
  = property (phi empty == 0)

prop_NonNegativePotential :: Queue Int -> Property
prop_NonNegativePotential q
  = property (phi q >= 0)


prop_AmortizedEnqueue ::  Int -> Queue Int -> Property
prop_AmortizedEnqueue x q =
  property (enqueueT x q + phi (enqueue x q) - phi q <= 2)

prop_AmortizedDequeue ::  Queue Int -> Property
prop_AmortizedDequeue q =
  not (isEmpty q) ==>
  property (dequeueT q + phi (dequeue q) - phi q <= 1)

-}
--- Template stuff
{-return []

runAllTests :: IO ()
runAllTests = $quickCheckAll >> return ()-}


