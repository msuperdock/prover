module Prover.Category.Split.Simple.Identity where

open import Prover.Category.Split
  using (split-functor-identity)
open import Prover.Category.Split.Simple
  using (SplitFunction; split-functor-simple)
open import Prover.Prelude

-- ## SplitFunction

split-function-identity
  : (A : Set)
  → SplitFunction A A
split-function-identity A
  = split-functor-simple
  $ split-functor-identity
    (split-functor-unit A)

