module Prover.Category.Simple where

open import Prover.Category
  using (Category; Functor)
open import Prover.Prelude

-- ## Function

Function
  : Set
  → Set
  → Set
Function A B
  = A → B

-- ## FunctionIdentity

FunctionIdentity
  : {A : Set}
  → Function A A
  → Set
FunctionIdentity {A = A} f
  = (x : A)
  → f x ≡ x

-- ## FunctionCompose

FunctionCompose
  : {A B C : Set}
  → Function B C
  → Function A B
  → Function A C
  → Set
FunctionCompose {A = A} f g h
  = (x : A)
  → h x ≡ f (g x)

-- ## FunctionSquare

FunctionSquare
  : {A₁ A₂ B₁ B₂ : Set}
  → Function A₁ A₂
  → Function B₁ B₂
  → Function A₁ B₁
  → Function A₂ B₂
  → Set
FunctionSquare {A₁ = A₁} f g h₁ h₂
  = (x₁ : A₁)
  → h₂ (f x₁) ≡ g (h₁ x₁)

-- ## PartialFunction

-- ### Definition

PartialFunction
  : Set
  → Set
  → Set
PartialFunction A B
  = A → Maybe B

-- ### Compose

partial-function-compose
  : {A B C : Set}
  → PartialFunction B C
  → PartialFunction A B
  → PartialFunction A C
partial-function-compose f g x
  = maybe (g x) nothing f

-- ## PartialDependentFunction

PartialDependentFunction
  : {A : Set}
  → (A → Set)
  → (A → Set)
  → Set
PartialDependentFunction {A = A} A' B'
  = (x : A)
  → (x' : A' x)
  → Maybe (B' x)

