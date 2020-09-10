module Prover.Function.Split.Compose where

open import Prover.Category.Split
  using (SplitFunctor; split-functor-compose)
open import Prover.Category.Split.Unit
  using (split-functor-unit)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Prelude

-- ## SplitFunction

split-function-compose
  : {A B C : Set}
  → SplitFunction B C
  → SplitFunction A B
  → SplitFunction A C
split-function-compose F G
  = SplitFunctor.split-function
  $ split-functor-compose
    (split-functor-unit F)
    (split-functor-unit G)

