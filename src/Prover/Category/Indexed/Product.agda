module Prover.Category.Indexed.Product where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedDependentFunctorCompose; IndexedDependentFunctorIdentity;
    IndexedDependentFunctorSquare; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; empty; indexed-category₀;
    indexed-dependent-category; indexed-dependent-functor;
    indexed-dependent-functor-compose; indexed-dependent-functor-identity;
    indexed-dependent-functor-square; indexed-functor₀;
    indexed-functor-compose₀; indexed-functor-identity₀;
    indexed-functor-square₀; sigma)
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

-- ### IndexedDependentCategory

indexed-dependent-category-product
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → IndexedDependentCategory C'
  → IndexedDependentCategory C'
  → IndexedDependentCategory C'

-- ### IndexedDependentFunctor

indexed-dependent-functor-product
  : {n : ℕ}
  → {C D : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {C₁'' C₂'' : IndexedDependentCategory C'}
  → {D₁'' D₂'' : IndexedDependentCategory D'}
  → {F : ChainDependentFunctor C' D'}
  → IndexedDependentFunctor C₁'' D₁'' F
  → IndexedDependentFunctor C₂'' D₂'' F
  → IndexedDependentFunctor
    (indexed-dependent-category-product C₁'' C₂'')
    (indexed-dependent-category-product D₁'' D₂'') F

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-product
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C₁'' C₂'' : IndexedDependentCategory C'}
  → {F : ChainDependentFunctor C' C'}
  → {F₁' : IndexedDependentFunctor C₁'' C₁'' F}
  → {F₂' : IndexedDependentFunctor C₂'' C₂'' F}
  → IndexedDependentFunctorIdentity F₁'
  → IndexedDependentFunctorIdentity F₂'
  → IndexedDependentFunctorIdentity
    (indexed-dependent-functor-product F₁' F₂')

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-product
  : {n : ℕ}
  → {C D E : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {E' : ChainDependentCategory E n}
  → {C₁'' C₂'' : IndexedDependentCategory C'}
  → {D₁'' D₂'' : IndexedDependentCategory D'}
  → {E₁'' E₂'' : IndexedDependentCategory E'}
  → {F : ChainDependentFunctor D' E'}
  → {G : ChainDependentFunctor C' D'}
  → {H : ChainDependentFunctor C' E'}
  → {F₁' : IndexedDependentFunctor D₁'' E₁'' F}
  → {F₂' : IndexedDependentFunctor D₂'' E₂'' F}
  → {G₁' : IndexedDependentFunctor C₁'' D₁'' G}
  → {G₂' : IndexedDependentFunctor C₂'' D₂'' G}
  → {H₁' : IndexedDependentFunctor C₁'' E₁'' H}
  → {H₂' : IndexedDependentFunctor C₂'' E₂'' H}
  → IndexedDependentFunctorCompose F₁' G₁' H₁'
  → IndexedDependentFunctorCompose F₂' G₂' H₂'
  → IndexedDependentFunctorCompose
    (indexed-dependent-functor-product F₁' F₂')
    (indexed-dependent-functor-product G₁' G₂')
    (indexed-dependent-functor-product H₁' H₂')

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-product
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : Category}
  → {C₁' : ChainDependentCategory C₁ n}
  → {C₂' : ChainDependentCategory C₂ n}
  → {D₁' : ChainDependentCategory D₁ n}
  → {D₂' : ChainDependentCategory D₂ n}
  → {C₁₁'' C₁₂'' : IndexedDependentCategory C₁'}
  → {C₂₁'' C₂₂'' : IndexedDependentCategory C₂'}
  → {D₁₁'' D₁₂'' : IndexedDependentCategory D₁'}
  → {D₂₁'' D₂₂'' : IndexedDependentCategory D₂'}
  → {F : ChainDependentFunctor C₁' C₂'}
  → {G : ChainDependentFunctor D₁' D₂'}
  → {H₁ : ChainDependentFunctor C₁' D₁'}
  → {H₂ : ChainDependentFunctor C₂' D₂'}
  → {F₁' : IndexedDependentFunctor C₁₁'' C₂₁'' F}
  → {F₂' : IndexedDependentFunctor C₁₂'' C₂₂'' F}
  → {G₁' : IndexedDependentFunctor D₁₁'' D₂₁'' G}
  → {G₂' : IndexedDependentFunctor D₁₂'' D₂₂'' G}
  → {H₁₁' : IndexedDependentFunctor C₁₁'' D₁₁'' H₁}
  → {H₁₂' : IndexedDependentFunctor C₁₂'' D₁₂'' H₁}
  → {H₂₁' : IndexedDependentFunctor C₂₁'' D₂₁'' H₂}
  → {H₂₂' : IndexedDependentFunctor C₂₂'' D₂₂'' H₂}
  → IndexedDependentFunctorSquare F₁' G₁' H₁₁' H₂₁'
  → IndexedDependentFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → IndexedDependentFunctorSquare
    (indexed-dependent-functor-product F₁' F₂')
    (indexed-dependent-functor-product G₁' G₂')
    (indexed-dependent-functor-product H₁₁' H₁₂')
    (indexed-dependent-functor-product H₂₁' H₂₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-product
  {n = zero} C₁' C₂'
  = empty
    (category-product
      (indexed-category₀ C₁')
      (indexed-category₀ C₂'))
indexed-category-product
  {n = suc _} C₁' C₂'
  = sigma
    (indexed-dependent-category-product
      (IndexedCategory.unpack C₁')
      (IndexedCategory.unpack C₂'))

-- ### IndexedFunctor

indexed-functor-product
  {n = zero}
  {C₁' = C₁'} {C₂' = C₂'} {D₁' = D₁'} {D₂' = D₂'} F₁' F₂'
  = empty
    (functor-product
      {C₁ = indexed-category₀ C₁'}
      {C₂ = indexed-category₀ C₂'}
      {D₁ = indexed-category₀ D₁'}
      {D₂ = indexed-category₀ D₂'}
      (indexed-functor₀ F₁')
      (indexed-functor₀ F₂'))
indexed-functor-product
  {n = suc _} F₁' F₂'
  = sigma
    (indexed-dependent-functor-product
      (IndexedFunctor.unpack F₁')
      (IndexedFunctor.unpack F₂'))

-- ### IndexedFunctorIdentity

indexed-functor-identity-product
  {n = zero}
  {C₁' = C₁'} {C₂' = C₂'}
  {F₁' = F₁'} {F₂' = F₂'} p₁ p₂
  = empty
    (functor-identity-product
      {C₁ = indexed-category₀ C₁'}
      {C₂ = indexed-category₀ C₂'}
      {F₁ = indexed-functor₀ F₁'}
      {F₂ = indexed-functor₀ F₂'}
      (indexed-functor-identity₀ p₁)
      (indexed-functor-identity₀ p₂))
indexed-functor-identity-product
  {n = suc _} p₁ p₂
  = sigma
    (indexed-dependent-functor-identity-product
      (IndexedFunctorIdentity.unpack p₁)
      (IndexedFunctorIdentity.unpack p₂))

indexed-functor-identity-product-eq _ _ _ refl
  = indexed-functor-identity-product

-- ### IndexedFunctorCompose

indexed-functor-compose-product
  {n = zero}
  {C₁' = C₁'} {C₂' = C₂'} {D₁' = D₁'} {D₂' = D₂'} {E₁' = E₁'} {E₂' = E₂'}
  {F₁' = F₁'} {F₂' = F₂'} {G₁' = G₁'} {G₂' = G₂'} {H₁' = H₁'} {H₂' = H₂'}
  p₁ p₂
  = empty
    (functor-compose-product
      {C₁ = indexed-category₀ C₁'}
      {C₂ = indexed-category₀ C₂'}
      {D₁ = indexed-category₀ D₁'}
      {D₂ = indexed-category₀ D₂'}
      {E₁ = indexed-category₀ E₁'}
      {E₂ = indexed-category₀ E₂'}
      {F₁ = indexed-functor₀ F₁'}
      {F₂ = indexed-functor₀ F₂'}
      {G₁ = indexed-functor₀ G₁'}
      {G₂ = indexed-functor₀ G₂'}
      {H₁ = indexed-functor₀ H₁'}
      {H₂ = indexed-functor₀ H₂'}
      (indexed-functor-compose₀ p₁)
      (indexed-functor-compose₀ p₂))
indexed-functor-compose-product
  {n = suc _} p₁ p₂
  = sigma
    (indexed-dependent-functor-compose-product
      (IndexedFunctorCompose.unpack p₁)
      (IndexedFunctorCompose.unpack p₂))

indexed-functor-compose-product-eq _ _ _ refl
  = indexed-functor-compose-product

-- ### IndexedFunctorSquare

indexed-functor-square-product
  {n = zero}
  {C₁₁' = C₁₁'} {C₁₂' = C₁₂'} {C₂₁' = C₂₁'} {C₂₂' = C₂₂'}
  {D₁₁' = D₁₁'} {D₁₂' = D₁₂'} {D₂₁' = D₂₁'} {D₂₂' = D₂₂'}
  {F₁' = F₁'} {F₂' = F₂'} {G₁' = G₁'} {G₂' = G₂'}
  {H₁₁' = H₁₁'} {H₁₂' = H₁₂'} {H₂₁' = H₂₁'} {H₂₂' = H₂₂'} s₁ s₂
  = empty
    (functor-square-product
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₁₂ = indexed-category₀ C₁₂'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {C₂₂ = indexed-category₀ C₂₂'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₁₂ = indexed-category₀ D₁₂'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {D₂₂ = indexed-category₀ D₂₂'}
      {F₁ = indexed-functor₀ F₁'}
      {F₂ = indexed-functor₀ F₂'}
      {G₁ = indexed-functor₀ G₁'}
      {G₂ = indexed-functor₀ G₂'}
      {H₁₁ = indexed-functor₀ H₁₁'}
      {H₁₂ = indexed-functor₀ H₁₂'}
      {H₂₁ = indexed-functor₀ H₂₁'}
      {H₂₂ = indexed-functor₀ H₂₂'}
      (indexed-functor-square₀ s₁)
      (indexed-functor-square₀ s₂))
indexed-functor-square-product
  {n = suc _} s₁ s₂
  = sigma
    (indexed-dependent-functor-square-product
      (IndexedFunctorSquare.unpack s₁)
      (IndexedFunctorSquare.unpack s₂))

indexed-functor-square-product-eq _ _ _ refl
  = indexed-functor-square-product

-- ### IndexedDependentCategory

indexed-dependent-category-product C₁'' C₂''
  = indexed-dependent-category
    (λ x → indexed-category-product
      (IndexedDependentCategory.indexed-category C₁'' x)
      (IndexedDependentCategory.indexed-category C₂'' x))
    (λ f → indexed-functor-product
      (IndexedDependentCategory.indexed-functor C₁'' f)
      (IndexedDependentCategory.indexed-functor C₂'' f))
    (λ x → indexed-functor-identity-product
      (IndexedDependentCategory.indexed-functor-identity C₁'' x)
      (IndexedDependentCategory.indexed-functor-identity C₂'' x))
    (λ f g → indexed-functor-compose-product
      (IndexedDependentCategory.indexed-functor-compose C₁'' f g)
      (IndexedDependentCategory.indexed-functor-compose C₂'' f g))

-- ### IndexedDependentFunctor

indexed-dependent-functor-product F₁' F₂'
  = indexed-dependent-functor
    (λ x → indexed-functor-product
      (IndexedDependentFunctor.indexed-functor F₁' x)
      (IndexedDependentFunctor.indexed-functor F₂' x))
    (λ f → indexed-functor-square-product
      (IndexedDependentFunctor.indexed-functor-square F₁' f)
      (IndexedDependentFunctor.indexed-functor-square F₂' f))

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-product
  {C' = C'} {C₁'' = C₁''} {C₂'' = C₂''} p₁ p₂
  = indexed-dependent-functor-identity
    (IndexedDependentFunctorIdentity.functor p₁)
    (λ x → indexed-functor-identity-product-eq
      (ChainDependentCategory.chain-category C')
      (IndexedDependentCategory.indexed-category C₁'')
      (IndexedDependentCategory.indexed-category C₂'')
      (IndexedDependentFunctorIdentity.base p₁ x)
      (IndexedDependentFunctorIdentity.indexed-functor p₁ x)
      (IndexedDependentFunctorIdentity.indexed-functor p₂ x))

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-product
  {E' = E'} {E₁'' = E₁''} {E₂'' = E₂''} p₁ p₂
  = indexed-dependent-functor-compose
    (IndexedDependentFunctorCompose.functor p₁)
    (λ x → indexed-functor-compose-product-eq
      (ChainDependentCategory.chain-category E')
      (IndexedDependentCategory.indexed-category E₁'')
      (IndexedDependentCategory.indexed-category E₂'')
      (IndexedDependentFunctorCompose.base p₁ x)
      (IndexedDependentFunctorCompose.indexed-functor p₁ x)
      (IndexedDependentFunctorCompose.indexed-functor p₂ x))

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-product
  {D₂' = D₂'} {D₂₁'' = D₂₁''} {D₂₂'' = D₂₂''} s₁ s₂
  = indexed-dependent-functor-square
    (IndexedDependentFunctorSquare.functor s₁)
    (λ x → indexed-functor-square-product-eq
      (ChainDependentCategory.chain-category D₂')
      (IndexedDependentCategory.indexed-category D₂₁'')
      (IndexedDependentCategory.indexed-category D₂₂'')
      (IndexedDependentFunctorSquare.base s₁ x)
      (IndexedDependentFunctorSquare.indexed-functor s₁ x)
      (IndexedDependentFunctorSquare.indexed-functor s₂ x))

