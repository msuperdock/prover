module Prover.Category.Split.Simple.Product where

open import Prover.Category.Split.Product
  using (split-functor-product)
open import Prover.Category.Split.Simple
  using (SplitFunction; split-functor-simple)
open import Prover.Category.Split.Unit
  using (split-functor-unit)
open import Prover.Prelude

-- ## SplitFunction

split-function-product
  : {A₁ A₂ B₁ B₂ : Set}
  → SplitFunction A₁ B₁
  → SplitFunction A₂ B₂
  → SplitFunction (A₁ × A₂) (B₁ × B₂)
split-function-product F₁ F₂
  = split-functor-simple
  $ split-functor-product
    (split-functor-unit F₁)
    (split-functor-unit F₂)

