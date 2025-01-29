module Data.Functor.TraverseSt

import Control.Monad.State

import Data.Colist
import Data.List.Lazy

%default total

-----------------
--- Interface ---
-----------------

||| A particular case of sub-traversability with the state monad.
|||
||| This is not a full traverse because the final state is not returned.
||| This allows us to implement this interface for (potentially) infinite data types.
|||
||| This interface has a law connecting to the `Functor` superinterface:
||| `traverseSt () $ const $ pure . f` must act as `map f`.
public export
interface Functor f => TraversableSt f where
  traverseSt : s -> (s -> a -> (s, b)) -> f a -> f b

--------------------------------------
--- Particular universal functions ---
--------------------------------------

public export %inline
withIndex : TraversableSt f => f a -> f (Nat, a)
withIndex = traverseSt Z $ \n, x => (S n, n, x)

public export %inline
(.withIndex) : TraversableSt f => f a -> f (Nat, a)
(.withIndex) = withIndex

------------------------------------------
--- Implementations for standard types ---
------------------------------------------

public export
TraversableSt Stream where
  traverseSt s f (x::xs) = do
    let (s', y) = f s x
    y :: traverseSt s' f xs

public export
TraversableSt Colist where
  traverseSt _ _ []      = []
  traverseSt s f (x::xs) = do
    let (s', y) = f s x
    y :: traverseSt s' f xs

public export
TraversableSt LazyList where
  traverseSt _ _ []      = []
  traverseSt s f (x::xs) = do
    let (s', y) = f s x
    y :: traverseSt s' f xs

public export
Traversable f => TraversableSt f where
  traverseSt s f = evalState s . traverse (ST . pure .: flip f)
