module Prover.Category.Indexed.Unit where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; cons; nil)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleFunctor; IndexedSimpleFunctorCompose;
    IndexedSimpleFunctorIdentity; IndexedSimpleFunctorSquare;
    IndexedSimpleCategory; indexed-simple-category₀; indexed-simple-functor₀;
    indexed-simple-functor-compose₀; indexed-simple-functor-identity₀;
    indexed-simple-functor-square₀)
open import Prover.Category.Unit
  using (category-unit; functor-compose-unit; functor-identity-unit;
    functor-square-unit; functor-unit)
open import Prover.Prelude

-- ## Types

-- ### IndexedCategory

indexed-category-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → IndexedCategory C

-- ### IndexedFunctor

indexed-functor-unit
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → {D' : IndexedSimpleCategory D}
  → {F : ChainFunctor C D}
  → IndexedSimpleFunctor C' D' F
  → IndexedFunctor
    (indexed-category-unit C')
    (indexed-category-unit D') F

-- ### IndexedFunctorIdentity

indexed-functor-identity-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → {F : ChainFunctor C C}
  → {F' : IndexedSimpleFunctor C' C' F}
  → IndexedSimpleFunctorIdentity F'
  → IndexedFunctorIdentity
    (indexed-functor-unit F')

indexed-functor-identity-unit-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → IndexedSimpleCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : IndexedSimpleFunctor (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → IndexedSimpleFunctorIdentity F'
  → IndexedFunctorIdentity
    (indexed-functor-unit F')

-- ### IndexedFunctorCompose

indexed-functor-compose-unit
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → {D' : IndexedSimpleCategory D}
  → {E' : IndexedSimpleCategory E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : IndexedSimpleFunctor D' E' F}
  → {G' : IndexedSimpleFunctor C' D' G}
  → {H' : IndexedSimpleFunctor C' E' H}
  → IndexedSimpleFunctorCompose F' G' H'
  → IndexedFunctorCompose
    (indexed-functor-unit F')
    (indexed-functor-unit G')
    (indexed-functor-unit H')

indexed-functor-compose-unit-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C' : IndexedSimpleCategory C}
  → {D' : IndexedSimpleCategory D}
  → (E' : (x : A) → IndexedSimpleCategory (E x))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F' : IndexedSimpleFunctor D' (E' x₁) F}
  → {G' : IndexedSimpleFunctor C' D' G}
  → {H' : IndexedSimpleFunctor C' (E' x₂) H}
  → x₂ ≡ x₁
  → IndexedSimpleFunctorCompose F' G' H'
  → IndexedFunctorCompose
    (indexed-functor-unit F')
    (indexed-functor-unit G')
    (indexed-functor-unit H')

-- ### IndexedFunctorSquare

indexed-functor-square-unit
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : IndexedSimpleCategory C₁}
  → {C₂' : IndexedSimpleCategory C₂}
  → {D₁' : IndexedSimpleCategory D₁}
  → {D₂' : IndexedSimpleCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : IndexedSimpleFunctor C₁' C₂' F}
  → {G' : IndexedSimpleFunctor D₁' D₂' G}
  → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
  → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
  → IndexedSimpleFunctorSquare F' G' H₁' H₂'
  → IndexedFunctorSquare
    (indexed-functor-unit F')
    (indexed-functor-unit G')
    (indexed-functor-unit H₁')
    (indexed-functor-unit H₂')

indexed-functor-square-unit-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁' : IndexedSimpleCategory C₁}
  → {C₂' : IndexedSimpleCategory C₂}
  → {D₁' : IndexedSimpleCategory D₁}
  → (D₂' : (x : A) → IndexedSimpleCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F' : IndexedSimpleFunctor C₁' C₂' F}
  → {G' : IndexedSimpleFunctor D₁' (D₂' x₁) G}
  → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
  → {H₂' : IndexedSimpleFunctor C₂' (D₂' x₂) H₂}
  → x₂ ≡ x₁
  → IndexedSimpleFunctorSquare F' G' H₁' H₂'
  → IndexedFunctorSquare
    (indexed-functor-unit F')
    (indexed-functor-unit G')
    (indexed-functor-unit H₁')
    (indexed-functor-unit H₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-unit
  {n = zero} C'
  = nil
    (category-unit
      (indexed-simple-category₀ C'))
indexed-category-unit
  {n = suc _} C'
  = cons
    (λ x → indexed-category-unit
      (IndexedSimpleCategory.tail C' x))
    (λ f → indexed-functor-unit
      (IndexedSimpleCategory.indexed-simple-functor C' f))
    (λ x → indexed-functor-identity-unit
      (IndexedSimpleCategory.indexed-simple-functor-identity C' x)) 
    (λ f g → indexed-functor-compose-unit
      (IndexedSimpleCategory.indexed-simple-functor-compose C' f g))

-- ### IndexedFunctor

indexed-functor-unit
  {n = zero} F'
  = nil
    (functor-unit
      (indexed-simple-functor₀ F'))
indexed-functor-unit
  {n = suc _} F'
  = cons
    (λ x → indexed-functor-unit
      (IndexedSimpleFunctor.tail F' x))
    (λ f → indexed-functor-square-unit
      (IndexedSimpleFunctor.indexed-simple-functor-square F' f))

-- ### IndexedFunctorIdentity

indexed-functor-identity-unit
  {n = zero} {F' = F'} p
  = nil
    (functor-identity-unit
      (indexed-simple-functor₀ F')
      (indexed-simple-functor-identity₀ p))
indexed-functor-identity-unit
  {n = suc _} {C = C} {C' = C'} p
  = cons
    (IndexedSimpleFunctorIdentity.head p)
    (λ x → indexed-functor-identity-unit-eq
      (ChainCategory.tail C)
      (IndexedSimpleCategory.tail C')
      (IndexedSimpleFunctorIdentity.base p x)
      (IndexedSimpleFunctorIdentity.tail p x))

indexed-functor-identity-unit-eq _ _ refl
  = indexed-functor-identity-unit

-- ### IndexedFunctorCompose

indexed-functor-compose-unit
  {n = zero} {F' = F'} {G' = G'} {H' = H'} p
  = nil
    (functor-compose-unit
      (indexed-simple-functor₀ F')
      (indexed-simple-functor₀ G')
      (indexed-simple-functor₀ H')
      (indexed-simple-functor-compose₀ p))
indexed-functor-compose-unit
  {n = suc _} {E = E} {E' = E'} p
  = cons
    (IndexedSimpleFunctorCompose.head p)
    (λ x → indexed-functor-compose-unit-eq
      (ChainCategory.tail E)
      (IndexedSimpleCategory.tail E')
      (IndexedSimpleFunctorCompose.base p x)
      (IndexedSimpleFunctorCompose.tail p x))

indexed-functor-compose-unit-eq _ _ refl
  = indexed-functor-compose-unit

-- ### IndexedFunctorSquare

indexed-functor-square-unit
  {n = zero} {F' = F'} {G' = G'} {H₁' = H₁'} {H₂' = H₂'} s
  = nil
    (functor-square-unit
      (indexed-simple-functor₀ F')
      (indexed-simple-functor₀ G')
      (indexed-simple-functor₀ H₁')
      (indexed-simple-functor₀ H₂')
      (indexed-simple-functor-square₀ s))
indexed-functor-square-unit
  {n = suc _} {D₂ = D₂} {D₂' = D₂'} s
  = cons
    (IndexedSimpleFunctorSquare.head s)
    (λ x₁ → indexed-functor-square-unit-eq
      (ChainCategory.tail D₂)
      (IndexedSimpleCategory.tail D₂')
      (IndexedSimpleFunctorSquare.base s x₁)
      (IndexedSimpleFunctorSquare.tail s x₁))

indexed-functor-square-unit-eq _ _ refl
  = indexed-functor-square-unit

