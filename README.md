<!-- idris
module README

import Data.Functor.TraverseSt
import Data.Nat
import Data.Stream
import Data.Vect

import Control.Monad.State -- to make traverses to be reducible at compile time, workaround of #2439

%default total
%hide Data.Vect.Stream.take
-->

# Weaker traversals

Traversals for Idris 2 that are weaker than `Traversable` and thus more broadly applicable, e.g. to infinite data types

## Main idea

Sometimes we need to map elements of a data structure like list while preserving and tracking some state during that process.
Imagine a sequence of events, each involving some random seed which changes after management of such event.

We can use `traverse` from `Traversable` interface for this and manage such state in the `State` monad.

But not all data types which we may want to map like this implement `Traversable`.
Very common example (at least for Idris language) is `LazyList`.
Imagine also, for instance, infinite types like `Stream` or possibly infinite ones like `Colist`.
They all are not universally traversable, because (at least in Idris) `Applicative` cannot preserve laziness.
But these data types still can be traversed over state still preserving their laziness and infiniteness.

That's why we introduce `TraversableSt` interface, which allows mapping using state preserving the original data type.
It is meant to be between `Functor` and `Traversable` in interfaces hierarchy.

Consider some usage examples.

## Examples

Let's consider we have some values we want to map statefully in different ways:

```idris
numsList : List Nat
numsList = [1, 10, 2, 20]

strStream : Stream String
strStream = iterate (++ "b") "a"   -- "a" :: "ab" :: "abb" :: "abbb" :: ...
```

### Inits

Let's collect all inits of a given list-like data type:

```idris
inits : TraversableSt f => f a -> f (SnocList a)
inits = traverseSt [<] $ \prevInits, x => let is = prevInits :< x in (is, is)
```

And apply it:

```idris
nInits : List (SnocList Nat)
nInits = inits numsList

sInits : Stream (SnocList String)
sInits = inits strStream
```

Please notice that outer type is preserved, i.e. produced `sInits` is indeed an infinite `Stream`.

Let's check that everything looks like we expect:

```idris
nInitsCorrect : README.nInits = [[<1], [<1, 10], [<1, 10, 2], [<1, 10, 2, 20]]
nInitsCorrect = Refl

sInitsCorrect : take 4 README.sInits =
  [[<"a"], [<"a", "ab"], [<"a", "ab", "abb"], [<"a", "ab", "abb", "abbb"]]
sInitsCorrect = Refl
```

### Aggregation

Let's aggregate all values using `Monoid`:

```idris
aggregate : Monoid a => TraversableSt f => f a -> f a
aggregate = traverseSt neutral $ \sum, curr => let next = sum <+> curr in (next, next)
```

Let's check that is works:

```idris
nAggregateCorrect : aggregate @{Additive} README.numsList = [1, 11, 13, 33]
nAggregateCorrect = Refl

nAggregateCorrect' : aggregate @{Multiplicative} README.numsList = [1, 10, 20, 400]
nAggregateCorrect' = Refl

nAggregateCorrect'' : aggregate @{Maximum} README.numsList = [1, 10, 10, 20]
nAggregateCorrect'' = Refl

sAggregateCorrect : take 4 (aggregate README.strStream) = ["a", "aab", "aababb", "aababbabbb"]
sAggregateCorrect = Refl
```

### Ticking

Leave every third element, everything else convert to `Nothing`.
This example is to show a situation when intermediate state does not go to the resulting value.

```idris
leaveEvery3rd : TraversableSt f => f a -> f $ Maybe a
leaveEvery3rd = traverseSt 1 $
  \n, x => (S n, if modNatNZ n 3 %search == 0 then Just x else Nothing)
```

Let's check:

```idris
nL3Correct : leaveEvery3rd README.numsList = [Nothing, Nothing, Just 2, Nothing]
nL3Correct = Refl

sL3Correct : take 4 (leaveEvery3rd README.strStream) = [Nothing, Nothing, Just "abb", Nothing]
sL3Correct = Refl
```

### Sliding window

Consider an example when we want to map each element of a list-like structure with a sliding window if fixed size.
We will have initial fill of a sliding window as an argument for simplicity.

```idris
slidingWindow : TraversableSt f =>
                (initial : a) ->
                (n : Nat) -> IsSucc n =>
                f a -> f (Vect n a)
slidingWindow i (S _) = traverseSt (replicate _ i) $
  \win, x => let next = tail win `snoc` x in (next, next)
```

Let's check:

```idris
nSlidingCorrect : slidingWindow 0 3 README.numsList =
  [ [0 , 0 , 1 ]
  , [0 , 1 , 10]
  , [1 , 10, 2 ]
  , [10, 2 , 20]
  ]
nSlidingCorrect = Refl

sSlidingCorrect : take 5 (slidingWindow "" 4 README.strStream) =
  [ [""  , ""   , ""    , "a"    ]
  , [""  , ""   , "a"   , "ab"   ]
  , [""  , "a"  , "ab"  , "abb"  ]
  , ["a" , "ab" , "abb" , "abbb" ]
  , ["ab", "abb", "abbb", "abbbb"]
  ]
sSlidingCorrect = Refl
```

## Special traversals

Some special traversals are also present in this library.
For example, this library contains `withIndex` function that adds natural index to every element in the order of traversal:

```idris
nWithIndexCorrect : withIndex README.numsList = [(0, 1), (1, 10), (2, 2), (3, 20)]
nWithIndexCorrect = Refl

sWithIndexCorrect : take 4 (withIndex README.strStream) =
  [(0, "a"), (1, "ab"), (2, "abb"), (3, "abbb")]
sWithIndexCorrect = Refl
```
