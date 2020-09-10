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

module FunctionIdentity'
  (A : Set)
  where

  base
    : A
    → A
  base
    = id

function-identity
  : (A : Set)
  → Function A A
function-identity A
  = record {FunctionIdentity' A}

-- ### Compose

module _
  {A B C : Set}
  where

  module FunctionCompose'
    (F : Function B C)
    (G : Function A B)
    where

    base
      : A
      → C
    base
      = Function.base F
      ∘ Function.base G

  function-compose
    : Function B C
    → Function A B
    → Function A C
  function-compose F G
    = record {FunctionCompose' F G}

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

-- ### Identity

module _
  {A₁ A₂ : Set}
  where

  module FunctionSquareIdentity
    (F : Function A₁ A₂)
    where

    base
      : (x₁ : A₁)
      → Function.base (function-identity A₂) (Function.base F x₁)
        ≅ Function.base F (Function.base (function-identity A₁) x₁)
    base _
      = refl

  function-square-identity
    : (F : Function A₁ A₂)
    → FunctionSquare F F
      (function-identity A₁)
      (function-identity A₂)
  function-square-identity F
    = record {FunctionSquareIdentity F}

-- ### Compose

module _
  {A₁ A₂ B₁ B₂ C₁ C₂ : Set}
  {F : Function A₁ A₂}
  {G : Function B₁ B₂}
  {H : Function C₁ C₂}
  {I₁ : Function B₁ C₁}
  {I₂ : Function B₂ C₂}
  {J₁ : Function A₁ B₁}
  {J₂ : Function A₂ B₂}
  where

  module FunctionSquareCompose
    (s : FunctionSquare G H I₁ I₂)
    (t : FunctionSquare F G J₁ J₂)
    where

    base
      : (x₁ : A₁)
      → Function.base (function-compose I₂ J₂) (Function.base F x₁)
        ≅ Function.base H (Function.base (function-compose I₁ J₁) x₁)
    base x₁
      with Function.base J₂ (Function.base F x₁)
      | FunctionSquare.base t x₁
    ... | _ | refl
      = FunctionSquare.base s
        (Function.base J₁ x₁)

  function-square-compose
    : FunctionSquare G H I₁ I₂
    → FunctionSquare F G J₁ J₂
    → FunctionSquare F H
      (function-compose I₁ J₁)
      (function-compose I₂ J₂)
  function-square-compose s t
    = record {FunctionSquareCompose s t}

