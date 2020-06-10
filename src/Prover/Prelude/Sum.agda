module Prover.Prelude.Sum where

open import Prover.Prelude.Bool
  using (Bool; false; true)

-- ## Definition

infixr 1 _⊔_

data _⊔_
  (A₁ : Set)
  (A₂ : Set)
  : Set
  where

  ι₁
    : A₁
    → A₁ ⊔ A₂

  ι₂
    : A₂
    → A₁ ⊔ A₂

Sum
  : Set
  → Set
  → Set
Sum
  = _⊔_

-- ## Module

module Sum where

  open _⊔_ public

  -- ### Interface

  is₁
    : {A₁ A₂ : Set}
    → A₁ ⊔ A₂
    → Bool
  is₁ (ι₁ _)
    = true
  is₁ (ι₂ _)
    = false

  is₂
    : {A₁ A₂ : Set}
    → A₁ ⊔ A₂
    → Bool
  is₂ (ι₁ _)
    = false
  is₂ (ι₂ _)
    = true

  sum
    : {A₁ A₂ B : Set}
    → A₁ ⊔ A₂
    → (A₁ → B)
    → (A₂ → B)
    → B
  sum (ι₁ x₁) f₁ _ 
    = f₁ x₁
  sum (ι₂ x₂) _ f₂
    = f₂ x₂

  map₁
    : {A₁ A₂ A₁' : Set}
    → (A₁ → A₁')
    → A₁ ⊔ A₂
    → A₁' ⊔ A₂
  map₁ f₁ (ι₁ x₁)
    = ι₁ (f₁ x₁)
  map₁ _ (ι₂ x₂)
    = ι₂ x₂

  map₂
    : {A₁ A₂ A₂' : Set}
    → (A₂ → A₂')
    → A₁ ⊔ A₂
    → A₁ ⊔ A₂'
  map₂ _ (ι₁ x₁)
    = ι₁ x₁
  map₂ f₁ (ι₂ x₂)
    = ι₂ (f₁ x₂)

-- ## Exports

open Sum public
  using (sum)

