module Prover.Function.Identity where

open import Prover.Category
  using (Functor; FunctorSquare; functor-identity'; functor-square-identity)
open import Prover.Category.Unit
  using (category-unit; functor-unit)
open import Prover.Function
  using (Function; FunctionSquare)
open import Prover.Prelude

-- ## Function

function-identity
  : (A : Set)
  → Function A A
function-identity A
  = Functor.function
  $ functor-identity'
    (category-unit A)

-- ## FunctionSquare

function-square-identity
  : {A₁ A₂ : Set}
  → (F : Function A₁ A₂)
  → FunctionSquare F F
    (function-identity A₁)
    (function-identity A₂)
function-square-identity F
  = FunctorSquare.function
  $ functor-square-identity
    (functor-unit F)

