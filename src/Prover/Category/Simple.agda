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

-- ## PartialRetraction

-- ### Definition

record PartialRetraction
  (A B : Set)
  : Set
  where

  field

    to
      : A
      → Maybe B

    from
      : B
      → A

    to-from
      : (y : B)
      → to (from y) ≡ just y

-- ### Conversion

module _
  {A B : Set}
  where

  module RetractionPartial
    (F : Retraction A B)
    where

    to
      : A
      → Maybe B
    to x
      = just (Retraction.to F x)

    from
      : B
      → A
    from
      = Retraction.from F

    to-from
      : (y : B)
      → to (from y) ≡ just y
    to-from y
      = sub just (Retraction.to-from F y)

  retraction-partial
    : Retraction A B
    → PartialRetraction A B
  retraction-partial F
    = record {RetractionPartial F}

-- ### Identity

partial-retraction-identity
  : (A : Set)
  → PartialRetraction A A
partial-retraction-identity A
  = retraction-partial
    (retraction-identity A)

-- ### Compose

module _
  {A B C : Set}
  where

  module PartialRetractionCompose
    (F : PartialRetraction B C)
    (G : PartialRetraction A B)
    where

    to
      : A
      → Maybe C
    to x
      with PartialRetraction.to G x
    ... | nothing
      = nothing
    ... | just y
      = PartialRetraction.to F y

    from
      : C
      → A
    from
      = PartialRetraction.from G
      ∘ PartialRetraction.from F

    to-from
      : (y : C)
      → to (from y) ≡ just y
    to-from y
      with PartialRetraction.to G (PartialRetraction.from G
        (PartialRetraction.from F y))
      | PartialRetraction.to-from G
        (PartialRetraction.from F y)
    ... | _ | refl
      = PartialRetraction.to-from F y

  partial-retraction-compose
    : PartialRetraction B C
    → PartialRetraction A B
    → PartialRetraction A C
  partial-retraction-compose F G
    = record {PartialRetractionCompose F G}

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

