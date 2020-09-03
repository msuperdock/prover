module Prover.Category.Indexed.Product where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; cons; indexed-category₀;
    indexed-functor₀; indexed-functor-compose₀; indexed-functor-identity₀;
    indexed-functor-square₀; nil)
open import Prover.Category.Product
  using (category-product; functor-compose-product; functor-identity-product;
    functor-product; functor-square-product)
open import Prover.Prelude

-- ## Types

-- ### IndexedCategory

indexed-category-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedCategory C
  → IndexedCategory C
  → IndexedCategory C

-- ### IndexedFunctor

indexed-functor-product
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁' C₂' : IndexedCategory C}
  → {D₁' D₂' : IndexedCategory D}
  → {F : ChainFunctor C D}
  → IndexedFunctor C₁' D₁' F
  → IndexedFunctor C₂' D₂' F
  → IndexedFunctor
    (indexed-category-product C₁' C₂')
    (indexed-category-product D₁' D₂') F

-- ### IndexedFunctorIdentity

indexed-functor-identity-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : IndexedCategory C}
  → {F : ChainFunctor C C}
  → {F₁' : IndexedFunctor C₁' C₁' F}
  → {F₂' : IndexedFunctor C₂' C₂' F}
  → IndexedFunctorIdentity F₁'
  → IndexedFunctorIdentity F₂'
  → IndexedFunctorIdentity
    (indexed-functor-product F₁' F₂')

indexed-functor-identity-product-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁' C₂' : (x : A) → IndexedCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F₁' : IndexedFunctor (C₁' x₁) (C₁' x₂) F}
  → {F₂' : IndexedFunctor (C₂' x₁) (C₂' x₂) F}
  → x₂ ≡ x₁
  → IndexedFunctorIdentity F₁'
  → IndexedFunctorIdentity F₂'
  → IndexedFunctorIdentity
    (indexed-functor-product F₁' F₂')

-- ### IndexedFunctorCompose

indexed-functor-compose-product
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C₁' C₂' : IndexedCategory C}
  → {D₁' D₂' : IndexedCategory D}
  → {E₁' E₂' : IndexedCategory E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F₁' : IndexedFunctor D₁' E₁' F}
  → {F₂' : IndexedFunctor D₂' E₂' F}
  → {G₁' : IndexedFunctor C₁' D₁' G}
  → {G₂' : IndexedFunctor C₂' D₂' G}
  → {H₁' : IndexedFunctor C₁' E₁' H}
  → {H₂' : IndexedFunctor C₂' E₂' H}
  → IndexedFunctorCompose F₁' G₁' H₁'
  → IndexedFunctorCompose F₂' G₂' H₂'
  → IndexedFunctorCompose
    (indexed-functor-product F₁' F₂')
    (indexed-functor-product G₁' G₂')
    (indexed-functor-product H₁' H₂')

indexed-functor-compose-product-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C₁' C₂' : IndexedCategory C}
  → {D₁' D₂' : IndexedCategory D}
  → (E₁' E₂' : (x : A) → IndexedCategory (E x))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F₁' : IndexedFunctor D₁' (E₁' x₁) F}
  → {F₂' : IndexedFunctor D₂' (E₂' x₁) F}
  → {G₁' : IndexedFunctor C₁' D₁' G}
  → {G₂' : IndexedFunctor C₂' D₂' G}
  → {H₁' : IndexedFunctor C₁' (E₁' x₂) H}
  → {H₂' : IndexedFunctor C₂' (E₂' x₂) H}
  → x₂ ≡ x₁
  → IndexedFunctorCompose F₁' G₁' H₁'
  → IndexedFunctorCompose F₂' G₂' H₂'
  → IndexedFunctorCompose
    (indexed-functor-product F₁' F₂')
    (indexed-functor-product G₁' G₂')
    (indexed-functor-product H₁' H₂')

-- ### IndexedFunctorSquare

indexed-functor-square-product
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁₁' C₁₂' : IndexedCategory C₁}
  → {C₂₁' C₂₂' : IndexedCategory C₂}
  → {D₁₁' D₁₂' : IndexedCategory D₁}
  → {D₂₁' D₂₂' : IndexedCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F₁' : IndexedFunctor C₁₁' C₂₁' F}
  → {F₂' : IndexedFunctor C₁₂' C₂₂' F}
  → {G₁' : IndexedFunctor D₁₁' D₂₁' G}
  → {G₂' : IndexedFunctor D₁₂' D₂₂' G}
  → {H₁₁' : IndexedFunctor C₁₁' D₁₁' H₁}
  → {H₁₂' : IndexedFunctor C₁₂' D₁₂' H₁}
  → {H₂₁' : IndexedFunctor C₂₁' D₂₁' H₂}
  → {H₂₂' : IndexedFunctor C₂₂' D₂₂' H₂}
  → IndexedFunctorSquare F₁' G₁' H₁₁' H₂₁'
  → IndexedFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → IndexedFunctorSquare
    (indexed-functor-product F₁' F₂')
    (indexed-functor-product G₁' G₂')
    (indexed-functor-product H₁₁' H₁₂')
    (indexed-functor-product H₂₁' H₂₂')

indexed-functor-square-product-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁₁' C₁₂' : IndexedCategory C₁}
  → {C₂₁' C₂₂' : IndexedCategory C₂}
  → {D₁₁' D₁₂' : IndexedCategory D₁}
  → (D₂₁' D₂₂' : (x : A) → IndexedCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F₁' : IndexedFunctor C₁₁' C₂₁' F}
  → {F₂' : IndexedFunctor C₁₂' C₂₂' F}
  → {G₁' : IndexedFunctor D₁₁' (D₂₁' x₁) G}
  → {G₂' : IndexedFunctor D₁₂' (D₂₂' x₁) G}
  → {H₁₁' : IndexedFunctor C₁₁' D₁₁' H₁}
  → {H₁₂' : IndexedFunctor C₁₂' D₁₂' H₁}
  → {H₂₁' : IndexedFunctor C₂₁' (D₂₁' x₂) H₂}
  → {H₂₂' : IndexedFunctor C₂₂' (D₂₂' x₂) H₂}
  → x₂ ≡ x₁
  → IndexedFunctorSquare F₁' G₁' H₁₁' H₂₁'
  → IndexedFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → IndexedFunctorSquare
    (indexed-functor-product F₁' F₂')
    (indexed-functor-product G₁' G₂')
    (indexed-functor-product H₁₁' H₁₂')
    (indexed-functor-product H₂₁' H₂₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-product
  {n = zero} C₁' C₂'
  = nil
    (category-product
      (indexed-category₀ C₁')
      (indexed-category₀ C₂'))
indexed-category-product
  {n = suc _} C₁' C₂'
  = cons
    (λ x → indexed-category-product
      (IndexedCategory.tail C₁' x)
      (IndexedCategory.tail C₂' x))
    (λ f → indexed-functor-product
      (IndexedCategory.indexed-functor C₁' f)
      (IndexedCategory.indexed-functor C₂' f))
    (λ x → indexed-functor-identity-product
      (IndexedCategory.indexed-functor-identity C₁' x)
      (IndexedCategory.indexed-functor-identity C₂' x))
    (λ f g → indexed-functor-compose-product
      (IndexedCategory.indexed-functor-compose C₁' f g)
      (IndexedCategory.indexed-functor-compose C₂' f g))

-- ### IndexedFunctor

indexed-functor-product
  {n = zero} F₁' F₂'
  = nil
    (functor-product
      (indexed-functor₀ F₁')
      (indexed-functor₀ F₂'))
indexed-functor-product
  {n = suc _} F₁' F₂'
  = cons
    (λ x → indexed-functor-product
      (IndexedFunctor.tail F₁' x)
      (IndexedFunctor.tail F₂' x))
    (λ f → indexed-functor-square-product
      (IndexedFunctor.indexed-functor-square F₁' f)
      (IndexedFunctor.indexed-functor-square F₂' f))

-- ### IndexedFunctorIdentity

indexed-functor-identity-product
  {n = zero} p₁ p₂
  = nil
    (functor-identity-product
      (indexed-functor-identity₀ p₁)
      (indexed-functor-identity₀ p₂))
indexed-functor-identity-product
  {n = suc _} {C = C} {C₁' = C₁'} {C₂' = C₂'} p₁ p₂
  = cons
    (IndexedFunctorIdentity.head p₁)
    (λ x → indexed-functor-identity-product-eq
      (ChainCategory.tail C)
      (IndexedCategory.tail C₁')
      (IndexedCategory.tail C₂')
      (IndexedFunctorIdentity.base p₁ x)
      (IndexedFunctorIdentity.tail p₁ x)
      (IndexedFunctorIdentity.tail p₂ x))

indexed-functor-identity-product-eq _ _ _ refl
  = indexed-functor-identity-product

-- ### IndexedFunctorCompose

indexed-functor-compose-product
  {n = zero} p₁ p₂
  = nil
    (functor-compose-product
      (indexed-functor-compose₀ p₁)
      (indexed-functor-compose₀ p₂))
indexed-functor-compose-product
  {n = suc _} {E = E} {E₁' = E₁'} {E₂' = E₂'} p₁ p₂
  = cons
    (IndexedFunctorCompose.head p₁)
    (λ x → indexed-functor-compose-product-eq
      (ChainCategory.tail E)
      (IndexedCategory.tail E₁')
      (IndexedCategory.tail E₂')
      (IndexedFunctorCompose.base p₁ x)
      (IndexedFunctorCompose.tail p₁ x)
      (IndexedFunctorCompose.tail p₂ x))

indexed-functor-compose-product-eq _ _ _ refl
  = indexed-functor-compose-product

-- ### IndexedFunctorSquare

indexed-functor-square-product
  {n = zero} s₁ s₂
  = nil
    (functor-square-product
      (indexed-functor-square₀ s₁)
      (indexed-functor-square₀ s₂))
indexed-functor-square-product
  {n = suc _} {D₂ = D₂} {D₂₁' = D₂₁'} {D₂₂' = D₂₂'} s₁ s₂
  = cons
    (IndexedFunctorSquare.head s₁)
    (λ x₁ → indexed-functor-square-product-eq
      (ChainCategory.tail D₂)
      (IndexedCategory.tail D₂₁')
      (IndexedCategory.tail D₂₂')
      (IndexedFunctorSquare.base s₁ x₁)
      (IndexedFunctorSquare.tail s₁ x₁)
      (IndexedFunctorSquare.tail s₂ x₁))

indexed-functor-square-product-eq _ _ _ refl
  = indexed-functor-square-product

