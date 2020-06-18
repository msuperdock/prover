module Prover.Category.Split.Base.Identity where

open import Prover.Category.Split
  using (split-functor-identity)
open import Prover.Category.Split.Base
  using (SplitFunction; split-functor-simple)
open import Prover.Category.Unit
  using (category-unit)
open import Prover.Prelude

-- ## SplitFunction

split-function-identity
  : (A : Set)
  → SplitFunction A A
split-function-identity A
  = split-functor-simple
  $ split-functor-identity
    (category-unit A)

