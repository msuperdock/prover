module Prover.Function.List where

open import Prover.Category
  using (Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.List
  using (functor-compose-list; functor-identity-list; functor-list;
    functor-square-list)
open import Prover.Category.Unit
  using (functor-compose-unit; functor-identity-unit; functor-square-unit;
    functor-unit)
open import Prover.Function
  using (Function; FunctionCompose; FunctionIdentity; FunctionSquare)
open import Prover.Prelude

-- ## Function

function-list
  : {A B : Set}
  → Function A B
  → Function (List A) (List B)
function-list F
  = Functor.function
  $ functor-list
    (functor-unit F)

-- ## FunctionIdentity

function-identity-list
  : {A : Set}
  → {F : Function A A}
  → FunctionIdentity F
  → FunctionIdentity
    (function-list F)
function-identity-list p
  = FunctorIdentity.function
  $ functor-identity-list
    (functor-identity-unit p)

-- ## FunctionCompose

function-compose-list
  : {A B C : Set}
  → {F : Function B C}
  → {G : Function A B}
  → {H : Function A C}
  → FunctionCompose F G H
  → FunctionCompose
    (function-list F)
    (function-list G)
    (function-list H)
function-compose-list p
  = FunctorCompose.function
  $ functor-compose-list
    (functor-compose-unit p)

-- ## FunctionSquare

function-square-list
  : {A₁ A₂ B₁ B₂ : Set}
  → {F : Function A₁ A₂}
  → {G : Function B₁ B₂}
  → {H₁ : Function A₁ B₁}
  → {H₂ : Function A₂ B₂}
  → FunctionSquare F G H₁ H₂
  → FunctionSquare
    (function-list F)
    (function-list G)
    (function-list H₁)
    (function-list H₂)
function-square-list s
  = FunctorSquare.function
  $ functor-square-list
    (functor-square-unit s)

