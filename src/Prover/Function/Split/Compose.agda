module Prover.Function.Split.Compose where

open import Prover.Category.Split
  using (split-functor-compose)
open import Prover.Category.Split.Unit
  using (split-functor-unit)
open import Prover.Function.Split
  using (SplitFunction; split-functor-base)
open import Prover.Prelude

-- ## SplitFunction

split-function-compose
  : {A B C : Set}
  → SplitFunction B C
  → SplitFunction A B
  → SplitFunction A C
split-function-compose F G
  = split-functor-base
  $ split-functor-compose
    (split-functor-unit F)
    (split-functor-unit G)

