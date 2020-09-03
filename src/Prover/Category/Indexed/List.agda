module Prover.Category.Indexed.List where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; cons; indexed-category₀;
    indexed-functor₀; indexed-functor-compose₀; indexed-functor-identity₀;
    indexed-functor-square₀; nil)
open import Prover.Category.List
  using (category-list; functor-compose-list; functor-identity-list;
    functor-list; functor-square-list)
open import Prover.Prelude

-- ## Types

-- ### IndexedCategory

indexed-category-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedCategory C
  → IndexedCategory C

-- ### IndexedFunctor

indexed-functor-list
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : IndexedCategory C}
  → {D' : IndexedCategory D}
  → {F : ChainFunctor C D}
  → IndexedFunctor C' D' F
  → IndexedFunctor
    (indexed-category-list C')
    (indexed-category-list D') F

-- ### IndexedFunctorIdentity

indexed-functor-identity-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedCategory C}
  → {F : ChainFunctor C C}
  → {F' : IndexedFunctor C' C' F}
  → IndexedFunctorIdentity F'
  → IndexedFunctorIdentity
    (indexed-functor-list F')

indexed-functor-identity-list-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → IndexedCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : IndexedFunctor (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → IndexedFunctorIdentity F'
  → IndexedFunctorIdentity
    (indexed-functor-list F')

-- ### IndexedFunctorCompose

indexed-functor-compose-list
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
  → IndexedFunctorCompose
    (indexed-functor-list F')
    (indexed-functor-list G')
    (indexed-functor-list H')

indexed-functor-compose-list-eq
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
  → IndexedFunctorCompose
    (indexed-functor-list F')
    (indexed-functor-list G')
    (indexed-functor-list H')

-- ### IndexedFunctorSquare

indexed-functor-square-list
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
  → IndexedFunctorSquare
    (indexed-functor-list F')
    (indexed-functor-list G')
    (indexed-functor-list H₁')
    (indexed-functor-list H₂')

indexed-functor-square-list-eq
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
  → IndexedFunctorSquare
    (indexed-functor-list F')
    (indexed-functor-list G')
    (indexed-functor-list H₁')
    (indexed-functor-list H₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-list
  {n = zero} C'
  = nil
    (category-list
      (indexed-category₀ C'))
indexed-category-list
  {n = suc _} C'
  = cons
    (λ x → indexed-category-list
      (IndexedCategory.tail C' x))
    (λ f → indexed-functor-list
      (IndexedCategory.indexed-functor C' f))
    (λ x → indexed-functor-identity-list
      (IndexedCategory.indexed-functor-identity C' x))
    (λ f g → indexed-functor-compose-list
      (IndexedCategory.indexed-functor-compose C' f g))

-- ### IndexedFunctor

indexed-functor-list
  {n = zero} F'
  = nil
    (functor-list
      (indexed-functor₀ F'))
indexed-functor-list
  {n = suc _} F'
  = cons
    (λ x → indexed-functor-list
      (IndexedFunctor.tail F' x))
    (λ f → indexed-functor-square-list
      (IndexedFunctor.indexed-functor-square F' f))

-- ### IndexedFunctorIdentity

indexed-functor-identity-list
  {n = zero} p
  = nil
    (functor-identity-list
      (indexed-functor-identity₀ p))
indexed-functor-identity-list
  {n = suc _} {C = C} {C' = C'} p
  = cons
    (IndexedFunctorIdentity.head p)
    (λ x → indexed-functor-identity-list-eq
      (ChainCategory.tail C)
      (IndexedCategory.tail C')
      (IndexedFunctorIdentity.base p x)
      (IndexedFunctorIdentity.tail p x))

indexed-functor-identity-list-eq _ _ refl
  = indexed-functor-identity-list

-- ### IndexedFunctorCompose

indexed-functor-compose-list
  {n = zero} p
  = nil
    (functor-compose-list
      (indexed-functor-compose₀ p))
indexed-functor-compose-list
  {n = suc _} {E = E} {E' = E'} p
  = cons
    (IndexedFunctorCompose.head p)
    (λ x → indexed-functor-compose-list-eq
      (ChainCategory.tail E)
      (IndexedCategory.tail E')
      (IndexedFunctorCompose.base p x)
      (IndexedFunctorCompose.tail p x))

indexed-functor-compose-list-eq _ _ refl
  = indexed-functor-compose-list

-- ### IndexedFunctorSquare

indexed-functor-square-list
  {n = zero} s
  = nil
    (functor-square-list
      (indexed-functor-square₀ s))
indexed-functor-square-list
  {n = suc _} {D₂ = D₂} {D₂' = D₂'} s
  = cons
    (IndexedFunctorSquare.head s)
    (λ x₁ → indexed-functor-square-list-eq
      (ChainCategory.tail D₂)
      (IndexedCategory.tail D₂')
      (IndexedFunctorSquare.base s x₁)
      (IndexedFunctorSquare.tail s x₁))

indexed-functor-square-list-eq _ _ refl
  = indexed-functor-square-list

