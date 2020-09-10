module Prover.Function.Equal where

open import Prover.Function
  using (Function; FunctionCompose; FunctionEqual; FunctionIdentity;
    FunctionSquare)
open import Prover.Function.Compose
  using (function-compose)
open import Prover.Function.Identity
  using (function-identity)

-- ## FunctionIdentity

function-identity-to-equal
  : {A₁ A₂ : Set}
  → {F : Function A₁ A₂}
  → FunctionIdentity F
  → FunctionEqual F (function-identity A₁)
function-identity-to-equal p
  = record {FunctionIdentity p}

-- ## FunctionCompose

function-compose-to-equal
  : {A B C₁ C₂ : Set}
  → {F : Function B C₁}
  → {G : Function A B}
  → {H : Function A C₂}
  → FunctionCompose F G H
  → FunctionEqual H (function-compose F G)
function-compose-to-equal p
  = record {FunctionCompose p}

-- ## FunctionSquare

function-square-to-equal
  : {A₁ A₂ B₁ B₂ B₃ : Set}
  → {F : Function A₁ A₂}
  → {G : Function B₁ B₃}
  → {H₁ : Function A₁ B₁}
  → {H₂ : Function A₂ B₂}
  → FunctionSquare F G H₁ H₂
  → FunctionEqual (function-compose H₂ F) (function-compose G H₁)
function-square-to-equal s
  = record {FunctionSquare s}

