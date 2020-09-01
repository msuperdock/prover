module Prover.Function.Split.List where

open import Prover.Category.Split.List
  using (split-functor-list)
open import Prover.Category.Split.Unit
  using (split-functor-unit)
open import Prover.Function.Split
  using (SplitFunction; split-functor-base)
open import Prover.Prelude

-- ## SplitFunction

split-function-list
  : {A B : Set}
  → SplitFunction A B
  → SplitFunction (List A) (List B)
split-function-list F
  = split-functor-base
  $ split-functor-list
    (split-functor-unit F)

