module Prover.Function where

open import Prover.Prelude

-- ## Function

-- ### Definition

record Function
  (A B : Set)
  : Set
  where

  constructor

    function

  field

    base
      : A
      → B

-- ### Identity

function-identity
  : (A : Set)
  → Function A A
function-identity _
  = record
  { base
    = id
  }

-- ### Compose

function-compose
  : {A B C : Set}
  → Function B C
  → Function A B
  → Function A C
function-compose F G
  = record
  { base
    = Function.base F
    ∘ Function.base G
  }

-- ## FunctionEqual

record FunctionEqual
  {A B₁ B₂ : Set}
  (F₁ : Function A B₁)
  (F₂ : Function A B₂)
  : Set
  where

  field

    base
      : (x : A)
      → Function.base F₁ x ≅ Function.base F₂ x

-- ## FunctionIdentity

-- ### Definition

record FunctionIdentity
  {A₁ A₂ : Set}
  (F : Function A₁ A₂)
  : Set
  where

  field

    base
      : (x₁ : A₁)
      → Function.base F x₁ ≅ x₁

-- ### Equality

function-identity-to-equal
  : {A₁ A₂ : Set}
  → {F : Function A₁ A₂}
  → FunctionIdentity F
  → FunctionEqual F (function-identity A₁)
function-identity-to-equal p
  = record {FunctionIdentity p}

-- ## FunctionCompose

-- ### Definition

record FunctionCompose
  {A B C₁ C₂ : Set}
  (F : Function B C₁)
  (G : Function A B)
  (H : Function A C₂)
  : Set
  where

  field

    base
      : (x : A)
      → Function.base H x ≅ Function.base F (Function.base G x)

-- ### Equality

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

-- ### Definition

record FunctionSquare
  {A₁ A₂ B₁ B₂ B₃ : Set}
  (F : Function A₁ A₂)
  (G : Function B₁ B₃)
  (H₁ : Function A₁ B₁)
  (H₂ : Function A₂ B₂)
  : Set
  where

  field

    base
      : (x₁ : A₁)
      → Function.base H₂ (Function.base F x₁)
        ≅ Function.base G (Function.base H₁ x₁)

-- ### Equality

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

