{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--ple" @-}

--
-- Purely functional queues a.k.a. "Batched queues"
-- O(1) amortized cost for all operations
--
module Queue where

import Language.Haskell.Liquid.ProofCombinators

-- front is in direct order
-- back is in reverse order
-- invariant: front is empty => back is also empty
-- use a newtype to allow custom instance declarations

-- Purely functional queues a.k.a. "Batched queues"

{-@ data Queue a = Queue { fr :: [a], bk :: {v:[a] | (len fr == 0) => (len v == 0)} } @-}
data Queue a = Queue [a] [a] 
                deriving Show

empty :: Queue a
empty = Queue [] []

{-@ reflect isEmpty @-}
{-@ isEmpty :: q:Queue a -> {v:Bool | v <=> (len (fr q) == 0)} @-}
isEmpty :: Queue a -> Bool
isEmpty (Queue fr bk) = null fr

-- add to the back 
{-@ reflect enqueue @-}
enqueue :: a -> Queue a -> Queue a
enqueue x (Queue fr bk) = makeQueue fr (x:bk)

-- front element
{-@ reflect front @-}
{-@ front :: q:{Queue a | len (fr q) > 0} -> a @-}
front :: Queue a -> a
front (Queue (x:fr) bk) = x
--front _      = error "empty queue"

-- remove the front
{-@ reflect dequeue @-}
{-@ dequeue :: q:{Queue a | len (fr q) > 0} -> Queue a @-}
dequeue :: Queue a -> Queue a
dequeue (Queue (x:fr) bk) = makeQueue fr bk 
--dequeue _                 = error "empty queue"

-- smart constructor
{-@ reflect makeQueue @-}
makeQueue :: [a] -> [a] -> Queue a
makeQueue [] bk = Queue (reverse bk) []
makeQueue fr bk = Queue fr bk

-------------------------------------------------------
-- Testing amortized bounds
-------------------------------------------------------
    
-- actual cost functions
{-@ reflect enqueueT @-}
{-@ enqueueT :: a -> Queue a -> {x:Int | x >= 1} @-}
enqueueT :: a -> Queue a -> Int
enqueueT x (Queue fr bk) = makeQueueT fr (x:bk)

{-@ reflect dequeueT @-}
{-@ dequeueT :: q:{Queue a | len (fr q) > 0} -> {x:Int | x >= 1} @-}
dequeueT :: Queue a -> Int
dequeueT (Queue (x:fr) bk) = makeQueueT fr bk   

{-@ reflect makeQueueT @-}
{-@ makeQueueT :: fr:[a] -> bk:[a] -> {x:Int | x >= 1} @-}
makeQueueT :: [a] -> [a] -> Int
makeQueueT [] bk = 1 + length bk
makeQueueT fr bk = 1

-- potential
{-@ reflect phi @-}
{-@ phi :: Queue a -> Nat @-}
phi :: Queue a -> Int
phi (Queue fr bk) = length bk 

{-@ ple enqueueP @-}
{-@ enqueueP :: x:a -> q:Queue a -> {enqueueT x q + phi (enqueue x q) - phi q <= 2} @-}
enqueueP :: a -> Queue a -> Proof
enqueueP x (Queue [] bk)  
    = enqueueT x (Queue [] bk) + phi (enqueue x (Queue [] bk)) - phi (Queue [] bk)
    -- using the definitions of enqueueT and enqueue
    === makeQueueT [] (x:bk) + phi (makeQueue [] (x:bk)) - phi (Queue [] bk)
    -- using the definiton of makeQueueT and makeQueue
    === 1 + length (x:bk) + phi (Queue (reverse (x:bk)) []) - phi (Queue [] bk)
    -- using the definition of phi (Queue fr bk)
    === 1 + length (x:bk) + length [] - length bk
    -- length [] = 0
    === 1 + length (x:bk) - length bk
    -- length (x:bk) = 1 + length bk
    === 1 + 1 + length bk - length bk
    === 2   -- <= 2
    *** QED
enqueueP x (Queue fr bk)
    = enqueueT x (Queue fr bk) + phi (enqueue x (Queue fr bk)) - phi (Queue fr bk)
    -- using the definitions of enqueueT and enqueue 
    === makeQueueT fr (x:bk) + phi (makeQueue fr (x:bk)) - phi (Queue fr bk)
    -- using the definitions of makeQueueT and makeQueue 
    === 1 + phi (Queue fr (x:bk)) - phi (Queue fr bk)
    -- using the definition of phi (Queue fr bk) 
    === 1 + length (x:bk) - length bk
    -- length (x:bk) = 1 + length bk
    === 1 + 1 + length bk - length bk
    === 2   -- <= 2
    *** QED

{-@ ple dequeueP @-}
{-@ dequeueP :: q:{Queue a | len (fr q) > 0} -> {dequeueT q + phi (dequeue q) - phi q <= 1} @-}
dequeueP :: Queue a -> Proof
dequeueP (Queue [x] bk)
    = dequeueT (Queue [x] bk) + phi (dequeue (Queue [x] bk)) - phi (Queue [x] bk)
    -- using the definitions of dequeueT and dequeue
    === makeQueueT [] bk + phi (makeQueue [] bk) - phi (Queue [x] bk)
    -- using the definitions of makeQueueT and makeQueue
    === 1 + length bk + phi (Queue (reverse bk) []) - phi (Queue [x] bk)
    -- using the definition of phi
    === 1 + length bk + length [] - length bk
    -- length [] = 0
    === 1   -- <= 1
    *** QED
dequeueP (Queue (x:fr) bk) 
    = dequeueT (Queue (x:fr) bk) + phi (dequeue (Queue (x:fr) bk)) - phi (Queue (x:fr) bk)
    === makeQueueT fr bk + phi (makeQueue fr bk) - phi (Queue (x:fr) bk)
    -- using the definitions of makeQueueT and makeQueue
    === 1 + phi (Queue fr bk) - phi (Queue (x:fr) bk)
    -- using the definition of phi (Queue fr bk)
    === 1 + length bk - length bk
    === 1   -- <= 1
    *** QED

    