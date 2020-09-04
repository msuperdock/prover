module Prover.Category.Dependent.List where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; cons; dependent-category₀;
    dependent-functor₀; dependent-functor-compose₀; dependent-functor-identity₀;
    dependent-functor-square₀; nil)
open import Prover.Category.List
  using (category-list; functor-compose-list; functor-identity-list;
    functor-list; functor-square-list)
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

dependent-category-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → DependentCategory C

-- ### DependentFunctor

dependent-functor-list
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {F : ChainFunctor C D}
  → DependentFunctor C' D' F
  → DependentFunctor
    (dependent-category-list C')
    (dependent-category-list D') F

-- ### DependentFunctorIdentity

dependent-functor-identity-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {F : ChainFunctor C C}
  → {F' : DependentFunctor C' C' F}
  → DependentFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-list F')

dependent-functor-identity-list-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → DependentCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : DependentFunctor (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → DependentFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-list F')

-- ### DependentFunctorCompose

dependent-functor-compose-list
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {E' : DependentCategory E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : DependentFunctor D' E' F}
  → {G' : DependentFunctor C' D' G}
  → {H' : DependentFunctor C' E' H}
  → DependentFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-list F')
    (dependent-functor-list G')
    (dependent-functor-list H')

dependent-functor-compose-list-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → (E' : (x : A) → DependentCategory (E x))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F' : DependentFunctor D' (E' x₁) F}
  → {G' : DependentFunctor C' D' G}
  → {H' : DependentFunctor C' (E' x₂) H}
  → x₂ ≡ x₁
  → DependentFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-list F')
    (dependent-functor-list G')
    (dependent-functor-list H')

-- ### DependentFunctorSquare

dependent-functor-square-list
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {D₁' : DependentCategory D₁}
  → {D₂' : DependentCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' D₂' G}
  → {H₁' : DependentFunctor C₁' D₁' H₁}
  → {H₂' : DependentFunctor C₂' D₂' H₂}
  → DependentFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-list F')
    (dependent-functor-list G')
    (dependent-functor-list H₁')
    (dependent-functor-list H₂')

dependent-functor-square-list-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {D₁' : DependentCategory D₁}
  → (D₂' : (x : A) → DependentCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' (D₂' x₁) G}
  → {H₁' : DependentFunctor C₁' D₁' H₁}
  → {H₂' : DependentFunctor C₂' (D₂' x₂) H₂}
  → x₂ ≡ x₁
  → DependentFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-list F')
    (dependent-functor-list G')
    (dependent-functor-list H₁')
    (dependent-functor-list H₂')

-- ## Definitions

-- ### DependentCategory

dependent-category-list
  {n = zero} C'
  = nil
    (category-list
      (dependent-category₀ C'))
dependent-category-list
  {n = suc _} C'
  = cons
    (λ x → dependent-category-list
      (DependentCategory.tail C' x))
    (λ f → dependent-functor-list
      (DependentCategory.dependent-functor C' f))
    (λ x → dependent-functor-identity-list
      (DependentCategory.dependent-functor-identity C' x))
    (λ f g → dependent-functor-compose-list
      (DependentCategory.dependent-functor-compose C' f g))

-- ### DependentFunctor

dependent-functor-list
  {n = zero} F'
  = nil
    (functor-list
      (dependent-functor₀ F'))
dependent-functor-list
  {n = suc _} F'
  = cons
    (λ x → dependent-functor-list
      (DependentFunctor.tail F' x))
    (λ f → dependent-functor-square-list
      (DependentFunctor.dependent-functor-square F' f))

-- ### DependentFunctorIdentity

dependent-functor-identity-list
  {n = zero} p
  = nil
    (functor-identity-list
      (dependent-functor-identity₀ p))
dependent-functor-identity-list
  {n = suc _} {C = C} {C' = C'} p
  = cons
    (DependentFunctorIdentity.head p)
    (λ x → dependent-functor-identity-list-eq
      (ChainCategory.tail C)
      (DependentCategory.tail C')
      (DependentFunctorIdentity.base p x)
      (DependentFunctorIdentity.tail p x))

dependent-functor-identity-list-eq _ _ refl
  = dependent-functor-identity-list

-- ### DependentFunctorCompose

dependent-functor-compose-list
  {n = zero} p
  = nil
    (functor-compose-list
      (dependent-functor-compose₀ p))
dependent-functor-compose-list
  {n = suc _} {E = E} {E' = E'} p
  = cons
    (DependentFunctorCompose.head p)
    (λ x → dependent-functor-compose-list-eq
      (ChainCategory.tail E)
      (DependentCategory.tail E')
      (DependentFunctorCompose.base p x)
      (DependentFunctorCompose.tail p x))

dependent-functor-compose-list-eq _ _ refl
  = dependent-functor-compose-list

-- ### DependentFunctorSquare

dependent-functor-square-list
  {n = zero} s
  = nil
    (functor-square-list
      (dependent-functor-square₀ s))
dependent-functor-square-list
  {n = suc _} {D₂ = D₂} {D₂' = D₂'} s
  = cons
    (DependentFunctorSquare.head s)
    (λ x₁ → dependent-functor-square-list-eq
      (ChainCategory.tail D₂)
      (DependentCategory.tail D₂')
      (DependentFunctorSquare.base s x₁)
      (DependentFunctorSquare.tail s x₁))

dependent-functor-square-list-eq _ _ refl
  = dependent-functor-square-list

