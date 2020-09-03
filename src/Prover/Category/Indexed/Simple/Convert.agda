module Prover.Category.Indexed.Simple.Convert where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; indexed-category₀;
    indexed-functor₀; indexed-functor-compose₀; indexed-functor-identity₀;
    indexed-functor-square₀)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleFunctor; IndexedSimpleFunctorCompose;
    IndexedSimpleFunctorIdentity; IndexedSimpleFunctorSquare;
    IndexedSimpleCategory; cons; nil)
open import Prover.Prelude

-- ## Types

-- ### IndexedCategory

indexed-category-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedCategory C
  → IndexedSimpleCategory C

-- ### IndexedFunctor

indexed-functor-simple
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : IndexedCategory C}
  → {D' : IndexedCategory D}
  → {F : ChainFunctor C D}
  → IndexedFunctor C' D' F
  → IndexedSimpleFunctor
    (indexed-category-simple C')
    (indexed-category-simple D') F

-- ### IndexedFunctorIdentity

indexed-functor-identity-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedCategory C}
  → {F : ChainFunctor C C}
  → {F' : IndexedFunctor C' C' F}
  → IndexedFunctorIdentity F'
  → IndexedSimpleFunctorIdentity
    (indexed-functor-simple F')

indexed-functor-identity-simple-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → IndexedCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : IndexedFunctor (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → IndexedFunctorIdentity F'
  → IndexedSimpleFunctorIdentity
    (indexed-functor-simple F')

-- ### IndexedFunctorCompose

indexed-functor-compose-simple
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : IndexedCategory C}
  → {D' : IndexedCategory D}
  → {E' : IndexedCategory E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : IndexedFunctor D' E' F}
  → {G' : IndexedFunctor C' D' G}
  → {H' : IndexedFunctor C' E' H}
  → IndexedFunctorCompose F' G' H'
  → IndexedSimpleFunctorCompose
    (indexed-functor-simple F')
    (indexed-functor-simple G')
    (indexed-functor-simple H')

indexed-functor-compose-simple-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C' : IndexedCategory C}
  → {D' : IndexedCategory D}
  → (E' : (x : A) → IndexedCategory (E x))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F' : IndexedFunctor D' (E' x₁) F}
  → {G' : IndexedFunctor C' D' G}
  → {H' : IndexedFunctor C' (E' x₂) H}
  → x₂ ≡ x₁
  → IndexedFunctorCompose F' G' H'
  → IndexedSimpleFunctorCompose
    (indexed-functor-simple F')
    (indexed-functor-simple G')
    (indexed-functor-simple H')

-- ### IndexedFunctorSquare

indexed-functor-square-simple
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : IndexedCategory C₁}
  → {C₂' : IndexedCategory C₂}
  → {D₁' : IndexedCategory D₁}
  → {D₂' : IndexedCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : IndexedFunctor C₁' C₂' F}
  → {G' : IndexedFunctor D₁' D₂' G}
  → {H₁' : IndexedFunctor C₁' D₁' H₁}
  → {H₂' : IndexedFunctor C₂' D₂' H₂}
  → IndexedFunctorSquare F' G' H₁' H₂'
  → IndexedSimpleFunctorSquare
    (indexed-functor-simple F')
    (indexed-functor-simple G')
    (indexed-functor-simple H₁')
    (indexed-functor-simple H₂')

indexed-functor-square-simple-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁' : IndexedCategory C₁}
  → {C₂' : IndexedCategory C₂}
  → {D₁' : IndexedCategory D₁}
  → (D₂' : (x : A) → IndexedCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F' : IndexedFunctor C₁' C₂' F}
  → {G' : IndexedFunctor D₁' (D₂' x₁) G}
  → {H₁' : IndexedFunctor C₁' D₁' H₁}
  → {H₂' : IndexedFunctor C₂' (D₂' x₂) H₂}
  → x₂ ≡ x₁
  → IndexedFunctorSquare F' G' H₁' H₂'
  → IndexedSimpleFunctorSquare
    (indexed-functor-simple F')
    (indexed-functor-simple G')
    (indexed-functor-simple H₁')
    (indexed-functor-simple H₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-simple
  {n = zero} C'
  = nil
    (Category.Object
      (indexed-category₀ C'))
indexed-category-simple
  {n = suc _} C'
  = cons
    (λ x → indexed-category-simple
      (IndexedCategory.tail C' x))
    (λ f → indexed-functor-simple
      (IndexedCategory.indexed-functor C' f))
    (λ x → indexed-functor-identity-simple
      (IndexedCategory.indexed-functor-identity C' x))
    (λ f g → indexed-functor-compose-simple
      (IndexedCategory.indexed-functor-compose C' f g))

-- ### IndexedFunctor

indexed-functor-simple
  {n = zero} F'
  = nil
    (Functor.base
      (indexed-functor₀ F'))
indexed-functor-simple
  {n = suc _} F'
  = cons
    (λ x → indexed-functor-simple
      (IndexedFunctor.tail F' x))
    (λ f → indexed-functor-square-simple
      (IndexedFunctor.indexed-functor-square F' f))

-- ### IndexedFunctorIdentity

indexed-functor-identity-simple
  {n = zero} p
  = nil
    (FunctorIdentity.base
      (indexed-functor-identity₀ p))
indexed-functor-identity-simple
  {n = suc _} {C = C} {C' = C'} p
  = cons
    (IndexedFunctorIdentity.head p)
    (λ x → indexed-functor-identity-simple-eq
      (ChainCategory.tail C)
      (IndexedCategory.tail C')
      (IndexedFunctorIdentity.base p x)
      (IndexedFunctorIdentity.tail p x))

indexed-functor-identity-simple-eq _ _ refl
  = indexed-functor-identity-simple

-- ### IndexedFunctorCompose

indexed-functor-compose-simple
  {n = zero} p
  = nil
    (FunctorCompose.base
      (indexed-functor-compose₀ p))
indexed-functor-compose-simple
  {n = suc _} {E = E} {E' = E'} p
  = cons
    (IndexedFunctorCompose.head p)
    (λ x → indexed-functor-compose-simple-eq
      (ChainCategory.tail E)
      (IndexedCategory.tail E')
      (IndexedFunctorCompose.base p x)
      (IndexedFunctorCompose.tail p x))

indexed-functor-compose-simple-eq _ _ refl
  = indexed-functor-compose-simple

-- ### IndexedFunctorSquare

indexed-functor-square-simple
  {n = zero} s
  = nil
    (FunctorSquare.base
      (indexed-functor-square₀ s))
indexed-functor-square-simple
  {n = suc _} {D₂ = D₂} {D₂' = D₂'} s
  = cons
    (IndexedFunctorSquare.head s)
    (λ x → indexed-functor-square-simple-eq
      (ChainCategory.tail D₂)
      (IndexedCategory.tail D₂')
      (IndexedFunctorSquare.base s x)
      (IndexedFunctorSquare.tail s x))

indexed-functor-square-simple-eq _ _ refl
  = indexed-functor-square-simple

