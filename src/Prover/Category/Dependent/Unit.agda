module Prover.Category.Dependent.Unit where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; cons; nil)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleFunctor; DependentSimpleFunctorCompose;
    DependentSimpleFunctorIdentity; DependentSimpleFunctorSquare;
    DependentSimpleCategory; dependent-simple-category₀;
    dependent-simple-functor₀; dependent-simple-functor-compose₀;
    dependent-simple-functor-identity₀; dependent-simple-functor-square₀)
open import Prover.Category.Unit
  using (category-unit; functor-compose-unit; functor-identity-unit;
    functor-square-unit; functor-unit)
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

dependent-category-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentCategory C

-- ### DependentFunctor

dependent-functor-unit
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {F : ChainFunctor C D}
  → DependentSimpleFunctor C' D' F
  → DependentFunctor
    (dependent-category-unit C')
    (dependent-category-unit D') F

-- ### DependentFunctorIdentity

dependent-functor-identity-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {F : ChainFunctor C C}
  → {F' : DependentSimpleFunctor C' C' F}
  → DependentSimpleFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-unit F')

dependent-functor-identity-unit-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → DependentSimpleCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : DependentSimpleFunctor (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → DependentSimpleFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-unit F')

-- ### DependentFunctorCompose

dependent-functor-compose-unit
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {E' : DependentSimpleCategory E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : DependentSimpleFunctor D' E' F}
  → {G' : DependentSimpleFunctor C' D' G}
  → {H' : DependentSimpleFunctor C' E' H}
  → DependentSimpleFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-unit F')
    (dependent-functor-unit G')
    (dependent-functor-unit H')

dependent-functor-compose-unit-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → (E' : (x : A) → DependentSimpleCategory (E x))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F' : DependentSimpleFunctor D' (E' x₁) F}
  → {G' : DependentSimpleFunctor C' D' G}
  → {H' : DependentSimpleFunctor C' (E' x₂) H}
  → x₂ ≡ x₁
  → DependentSimpleFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-unit F')
    (dependent-functor-unit G')
    (dependent-functor-unit H')

-- ### DependentFunctorSquare

dependent-functor-square-unit
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {D₁' : DependentSimpleCategory D₁}
  → {D₂' : DependentSimpleCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : DependentSimpleFunctor C₁' C₂' F}
  → {G' : DependentSimpleFunctor D₁' D₂' G}
  → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
  → {H₂' : DependentSimpleFunctor C₂' D₂' H₂}
  → DependentSimpleFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-unit F')
    (dependent-functor-unit G')
    (dependent-functor-unit H₁')
    (dependent-functor-unit H₂')

dependent-functor-square-unit-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {D₁' : DependentSimpleCategory D₁}
  → (D₂' : (x : A) → DependentSimpleCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F' : DependentSimpleFunctor C₁' C₂' F}
  → {G' : DependentSimpleFunctor D₁' (D₂' x₁) G}
  → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
  → {H₂' : DependentSimpleFunctor C₂' (D₂' x₂) H₂}
  → x₂ ≡ x₁
  → DependentSimpleFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-unit F')
    (dependent-functor-unit G')
    (dependent-functor-unit H₁')
    (dependent-functor-unit H₂')

-- ## Definitions

-- ### DependentCategory

dependent-category-unit
  {n = zero} C'
  = nil
    (category-unit
      (dependent-simple-category₀ C'))
dependent-category-unit
  {n = suc _} C'
  = cons
    (λ x → dependent-category-unit
      (DependentSimpleCategory.tail C' x))
    (λ f → dependent-functor-unit
      (DependentSimpleCategory.dependent-simple-functor C' f))
    (λ x → dependent-functor-identity-unit
      (DependentSimpleCategory.dependent-simple-functor-identity C' x)) 
    (λ f g → dependent-functor-compose-unit
      (DependentSimpleCategory.dependent-simple-functor-compose C' f g))

-- ### DependentFunctor

dependent-functor-unit
  {n = zero} F'
  = nil
    (functor-unit
      (dependent-simple-functor₀ F'))
dependent-functor-unit
  {n = suc _} F'
  = cons
    (λ x → dependent-functor-unit
      (DependentSimpleFunctor.tail F' x))
    (λ f → dependent-functor-square-unit
      (DependentSimpleFunctor.dependent-simple-functor-square F' f))

-- ### DependentFunctorIdentity

dependent-functor-identity-unit
  {n = zero} {F' = F'} p
  = nil
    (functor-identity-unit
      (dependent-simple-functor₀ F')
      (dependent-simple-functor-identity₀ p))
dependent-functor-identity-unit
  {n = suc _} {C = C} {C' = C'} p
  = cons
    (DependentSimpleFunctorIdentity.head p)
    (λ x → dependent-functor-identity-unit-eq
      (ChainCategory.tail C)
      (DependentSimpleCategory.tail C')
      (DependentSimpleFunctorIdentity.base p x)
      (DependentSimpleFunctorIdentity.tail p x))

dependent-functor-identity-unit-eq _ _ refl
  = dependent-functor-identity-unit

-- ### DependentFunctorCompose

dependent-functor-compose-unit
  {n = zero} {F' = F'} {G' = G'} {H' = H'} p
  = nil
    (functor-compose-unit
      (dependent-simple-functor₀ F')
      (dependent-simple-functor₀ G')
      (dependent-simple-functor₀ H')
      (dependent-simple-functor-compose₀ p))
dependent-functor-compose-unit
  {n = suc _} {E = E} {E' = E'} p
  = cons
    (DependentSimpleFunctorCompose.head p)
    (λ x → dependent-functor-compose-unit-eq
      (ChainCategory.tail E)
      (DependentSimpleCategory.tail E')
      (DependentSimpleFunctorCompose.base p x)
      (DependentSimpleFunctorCompose.tail p x))

dependent-functor-compose-unit-eq _ _ refl
  = dependent-functor-compose-unit

-- ### DependentFunctorSquare

dependent-functor-square-unit
  {n = zero} {F' = F'} {G' = G'} {H₁' = H₁'} {H₂' = H₂'} s
  = nil
    (functor-square-unit
      (dependent-simple-functor₀ F')
      (dependent-simple-functor₀ G')
      (dependent-simple-functor₀ H₁')
      (dependent-simple-functor₀ H₂')
      (dependent-simple-functor-square₀ s))
dependent-functor-square-unit
  {n = suc _} {D₂ = D₂} {D₂' = D₂'} s
  = cons
    (DependentSimpleFunctorSquare.head s)
    (λ x₁ → dependent-functor-square-unit-eq
      (ChainCategory.tail D₂)
      (DependentSimpleCategory.tail D₂')
      (DependentSimpleFunctorSquare.base s x₁)
      (DependentSimpleFunctorSquare.tail s x₁))

dependent-functor-square-unit-eq _ _ refl
  = dependent-functor-square-unit

