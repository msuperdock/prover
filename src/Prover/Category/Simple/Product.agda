module Prover.Category.Simple.Product where

open import Prover.Category
  using (Functor)
open import Prover.Category.Product
  using (functor-product)
open import Prover.Category.Simple
  using (Function)
open import Prover.Category.Unit
  using (functor-unit)
open import Prover.Prelude

-- ## Function

function-product
  : {A₁ A₂ B₁ B₂ : Set}
  → Function A₁ B₁
  → Function A₂ B₂
  → Function (A₁ × A₂) (B₁ × B₂)
function-product f₁ f₂
  = Functor.base
  $ functor-product
    (functor-unit f₁)
    (functor-unit f₂)

