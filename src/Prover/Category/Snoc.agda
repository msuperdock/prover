module Prover.Category.Snoc where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorIdentity;
    ChainFunctorSquare; chain-category₁; chain-functor₁; chain-functor-compose₁;
    chain-functor-identity₁; chain-functor-square₁; cons)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; dependent-category₀;
    dependent-functor₀; dependent-functor-compose₀; dependent-functor-identity₀;
    dependent-functor-square₀)
open import Prover.Prelude

-- ## Types

-- ### ChainCategory

chain-category-snoc
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → ChainCategory (suc n)

-- ### ChainFunctor

chain-functor-snoc
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {F : ChainFunctor C D}
  → DependentFunctor C' D' F
  → ChainFunctor
    (chain-category-snoc C')
    (chain-category-snoc D')

-- ### ChainFunctorIdentity

chain-functor-identity-snoc
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {F : ChainFunctor C C}
  → {F' : DependentFunctor C' C' F}
  → DependentFunctorIdentity F'
  → ChainFunctorIdentity
    (chain-functor-snoc F')

chain-functor-identity-snoc-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → DependentCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : DependentFunctor (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → DependentFunctorIdentity F'
  → ChainFunctorIdentity
    (chain-functor-snoc F')

-- ### ChainFunctorCompose

chain-functor-compose-snoc
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
  → ChainFunctorCompose
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H')

chain-functor-compose-snoc-eq
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
  → ChainFunctorCompose
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H')

-- ### ChainFunctorSquare

chain-functor-square-snoc
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
  → ChainFunctorSquare
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H₁')
    (chain-functor-snoc H₂')

chain-functor-square-snoc-eq
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
  → ChainFunctorSquare
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H₁')
    (chain-functor-snoc H₂')

-- ## Definitions

-- ### ChainCategory

chain-category-snoc
  {n = zero} C'
  = chain-category₁
    (dependent-category₀ C')
chain-category-snoc
  {n = suc _} {C = C} C'
  = cons
    (ChainCategory.head C)
    (λ x → chain-category-snoc
      (DependentCategory.tail C' x))
    (λ f → chain-functor-snoc
      (DependentCategory.dependent-functor C' f))
    (λ x → chain-functor-identity-snoc
      (DependentCategory.dependent-functor-identity C' x))
    (λ f g → chain-functor-compose-snoc
      (DependentCategory.dependent-functor-compose C' f g))

-- ### ChainFunctor

chain-functor-snoc
  {n = zero} F'
  = chain-functor₁
    (dependent-functor₀ F')
chain-functor-snoc
  {n = suc _} {F = F} F'
  = cons
    (ChainFunctor.head F)
    (λ x → chain-functor-snoc
      (DependentFunctor.tail F' x))
    (λ f → chain-functor-square-snoc
      (DependentFunctor.dependent-functor-square F' f))

-- ### ChainFunctorIdentity

chain-functor-identity-snoc
  {n = zero} p
  = chain-functor-identity₁
    (dependent-functor-identity₀ p)
chain-functor-identity-snoc
  {n = suc _} {C = C} {C' = C'} p
  = cons
    (DependentFunctorIdentity.head p)
    (λ x → chain-functor-identity-snoc-eq
      (ChainCategory.tail C)
      (DependentCategory.tail C')
      (DependentFunctorIdentity.base p x)
      (DependentFunctorIdentity.tail p x))

chain-functor-identity-snoc-eq _ _ refl
  = chain-functor-identity-snoc

-- ### ChainFunctorCompose

chain-functor-compose-snoc
  {n = zero} p
  = chain-functor-compose₁
    (dependent-functor-compose₀ p)
chain-functor-compose-snoc
  {n = suc _} {E = E} {E' = E'} p
  = cons
    (DependentFunctorCompose.head p)
    (λ x → chain-functor-compose-snoc-eq
      (ChainCategory.tail E)
      (DependentCategory.tail E')
      (DependentFunctorCompose.base p x)
      (DependentFunctorCompose.tail p x))

chain-functor-compose-snoc-eq _ _ refl
  = chain-functor-compose-snoc

-- ### ChainFunctorSquare

chain-functor-square-snoc
  {n = zero} s
  = chain-functor-square₁
    (dependent-functor-square₀ s)
chain-functor-square-snoc
  {n = suc _} {D₂ = D₂} {D₂' = D₂'} s
  = cons
    (DependentFunctorSquare.head s)
    (λ x₁ → chain-functor-square-snoc-eq
      (ChainCategory.tail D₂)
      (DependentCategory.tail D₂')
      (DependentFunctorSquare.base s x₁)
      (DependentFunctorSquare.tail s x₁))

chain-functor-square-snoc-eq _ _ refl
  = chain-functor-square-snoc

