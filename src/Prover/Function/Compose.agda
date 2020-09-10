module Prover.Function.Compose where

open import Prover.Category
  using (Functor; FunctorSquare; functor-compose'; functor-square-compose)
open import Prover.Category.Unit
  using (functor-unit; functor-square-unit)
open import Prover.Function
  using (Function; FunctionSquare)
open import Prover.Prelude

-- ## Function

function-compose
  : {A B C : Set}
  → Function B C
  → Function A B
  → Function A C
function-compose F G
  = Functor.function
  $ functor-compose'
    (functor-unit F)
    (functor-unit G)

-- ## FunctionSquare

function-square-compose
  : {A₁ A₂ B₁ B₂ C₁ C₂ : Set}
  → {F : Function A₁ A₂}
  → {G : Function B₁ B₂}
  → {H : Function C₁ C₂}
  → {I₁ : Function B₁ C₁}
  → {I₂ : Function B₂ C₂}
  → {J₁ : Function A₁ B₁}
  → {J₂ : Function A₂ B₂}
  → FunctionSquare G H I₁ I₂
  → FunctionSquare F G J₁ J₂
  → FunctionSquare F H
    (function-compose I₁ J₁)
    (function-compose I₂ J₂)
function-square-compose s t
  = FunctorSquare.function
  $ functor-square-compose
    (functor-square-unit s)
    (functor-square-unit t)

