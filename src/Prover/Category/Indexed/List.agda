module Prover.Category.Indexed.List where

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

-- ### IndexedDependentCategory

indexed-dependent-category-list
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → IndexedDependentCategory C'
  → IndexedDependentCategory C'

-- ### IndexedDependentFunctor

indexed-dependent-functor-list
  : {n : ℕ}
  → {C D : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {C'' : IndexedDependentCategory C'}
  → {D'' : IndexedDependentCategory D'}
  → {F : ChainDependentFunctor C' D'}
  → IndexedDependentFunctor C'' D'' F
  → IndexedDependentFunctor
    (indexed-dependent-category-list C'')
    (indexed-dependent-category-list D'') F

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-list
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C'' : IndexedDependentCategory C'}
  → {F : ChainDependentFunctor C' C'}
  → {F' : IndexedDependentFunctor C'' C'' F}
  → IndexedDependentFunctorIdentity F'
  → IndexedDependentFunctorIdentity
    (indexed-dependent-functor-list F')

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-list
  : {n : ℕ}
  → {C D E : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {E' : ChainDependentCategory E n}
  → {C'' : IndexedDependentCategory C'}
  → {D'' : IndexedDependentCategory D'}
  → {E'' : IndexedDependentCategory E'}
  → {F : ChainDependentFunctor D' E'}
  → {G : ChainDependentFunctor C' D'}
  → {H : ChainDependentFunctor C' E'}
  → {F' : IndexedDependentFunctor D'' E'' F}
  → {G' : IndexedDependentFunctor C'' D'' G}
  → {H' : IndexedDependentFunctor C'' E'' H}
  → IndexedDependentFunctorCompose F' G' H'
  → IndexedDependentFunctorCompose
    (indexed-dependent-functor-list F')
    (indexed-dependent-functor-list G')
    (indexed-dependent-functor-list H')

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-list
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : Category}
  → {C₁' : ChainDependentCategory C₁ n}
  → {C₂' : ChainDependentCategory C₂ n}
  → {D₁' : ChainDependentCategory D₁ n}
  → {D₂' : ChainDependentCategory D₂ n}
  → {C₁'' : IndexedDependentCategory C₁'}
  → {C₂'' : IndexedDependentCategory C₂'}
  → {D₁'' : IndexedDependentCategory D₁'}
  → {D₂'' : IndexedDependentCategory D₂'}
  → {F : ChainDependentFunctor C₁' C₂'}
  → {G : ChainDependentFunctor D₁' D₂'}
  → {H₁ : ChainDependentFunctor C₁' D₁'}
  → {H₂ : ChainDependentFunctor C₂' D₂'}
  → {F' : IndexedDependentFunctor C₁'' C₂'' F}
  → {G' : IndexedDependentFunctor D₁'' D₂'' G}
  → {H₁' : IndexedDependentFunctor C₁'' D₁'' H₁}
  → {H₂' : IndexedDependentFunctor C₂'' D₂'' H₂}
  → IndexedDependentFunctorSquare F' G' H₁' H₂'
  → IndexedDependentFunctorSquare
    (indexed-dependent-functor-list F')
    (indexed-dependent-functor-list G')
    (indexed-dependent-functor-list H₁')
    (indexed-dependent-functor-list H₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-list
  {n = zero} C'
  = empty
    (category-list
      (indexed-category₀ C'))
indexed-category-list
  {n = suc _} C'
  = sigma
    (indexed-dependent-category-list
      (IndexedCategory.unpack C'))

-- ### IndexedFunctor

indexed-functor-list
  {n = zero}
  {C' = C'} {D' = D'} F'
  = empty
    (functor-list
      {C = indexed-category₀ C'}
      {D = indexed-category₀ D'}
      (indexed-functor₀ F'))
indexed-functor-list
  {n = suc _} F'
  = sigma
    (indexed-dependent-functor-list
      (IndexedFunctor.unpack F'))

-- ### IndexedFunctorIdentity

indexed-functor-identity-list
  {n = zero}
  {C' = C'}
  {F' = F'} p
  = empty
    (functor-identity-list
      {C = indexed-category₀ C'}
      {F = indexed-functor₀ F'}
      (indexed-functor-identity₀ p))
indexed-functor-identity-list
  {n = suc _} p
  = sigma
    (indexed-dependent-functor-identity-list
      (IndexedFunctorIdentity.unpack p))

indexed-functor-identity-list-eq _ _ refl
  = indexed-functor-identity-list

-- ### IndexedFunctorCompose

indexed-functor-compose-list
  {n = zero}
  {C' = C'} {D' = D'} {E' = E'}
  {F' = F'} {G' = G'} {H' = H'} p
  = empty
    (functor-compose-list
      {C = indexed-category₀ C'}
      {D = indexed-category₀ D'}
      {E = indexed-category₀ E'}
      {F = indexed-functor₀ F'}
      {G = indexed-functor₀ G'}
      {H = indexed-functor₀ H'}
      (indexed-functor-compose₀ p))
indexed-functor-compose-list
  {n = suc _} p
  = sigma
    (indexed-dependent-functor-compose-list
      (IndexedFunctorCompose.unpack p))

indexed-functor-compose-list-eq _ _ refl
  = indexed-functor-compose-list

-- ### IndexedFunctorSquare

indexed-functor-square-list
  {n = zero}
  {C₁' = C₁'} {C₂' = C₂'} {D₁' = D₁'} {D₂' = D₂'}
  {F' = F'} {G' = G'} {H₁' = H₁'} {H₂' = H₂'} s
  = empty
    (functor-square-list
      {C₁ = indexed-category₀ C₁'}
      {C₂ = indexed-category₀ C₂'}
      {D₁ = indexed-category₀ D₁'}
      {D₂ = indexed-category₀ D₂'}
      {F = indexed-functor₀ F'}
      {G = indexed-functor₀ G'}
      {H₁ = indexed-functor₀ H₁'}
      {H₂ = indexed-functor₀ H₂'}
      (indexed-functor-square₀ s))
indexed-functor-square-list
  {n = suc _} s
  = sigma
    (indexed-dependent-functor-square-list
      (IndexedFunctorSquare.unpack s))

indexed-functor-square-list-eq _ _ refl
  = indexed-functor-square-list

-- ### IndexedDependentCategory

indexed-dependent-category-list C''
  = indexed-dependent-category
    (λ x → indexed-category-list
      (IndexedDependentCategory.indexed-category C'' x))
    (λ f → indexed-functor-list
      (IndexedDependentCategory.indexed-functor C'' f))
    (λ x → indexed-functor-identity-list
      (IndexedDependentCategory.indexed-functor-identity C'' x))
    (λ f g → indexed-functor-compose-list
      (IndexedDependentCategory.indexed-functor-compose C'' f g))

-- ### IndexedDependentFunctor

indexed-dependent-functor-list F'
  = indexed-dependent-functor
    (λ x → indexed-functor-list
      (IndexedDependentFunctor.indexed-functor F' x))
    (λ f → indexed-functor-square-list
      (IndexedDependentFunctor.indexed-functor-square F' f))

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-list
  {C' = C'} {C'' = C''} p
  = indexed-dependent-functor-identity
    (IndexedDependentFunctorIdentity.functor p)
    (λ x → indexed-functor-identity-list-eq
      (ChainDependentCategory.chain-category C')
      (IndexedDependentCategory.indexed-category C'')
      (IndexedDependentFunctorIdentity.base p x)
      (IndexedDependentFunctorIdentity.indexed-functor p x))

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-list
  {E' = E'} {E'' = E''} p
  = indexed-dependent-functor-compose
    (IndexedDependentFunctorCompose.functor p)
    (λ x → indexed-functor-compose-list-eq
      (ChainDependentCategory.chain-category E')
      (IndexedDependentCategory.indexed-category E'')
      (IndexedDependentFunctorCompose.base p x)
      (IndexedDependentFunctorCompose.indexed-functor p x))

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-list
  {D₂' = D₂'} {D₂'' = D₂''} s
  = indexed-dependent-functor-square
    (IndexedDependentFunctorSquare.functor s)
    (λ x → indexed-functor-square-list-eq
      (ChainDependentCategory.chain-category D₂')
      (IndexedDependentCategory.indexed-category D₂'')
      (IndexedDependentFunctorSquare.base s x)
      (IndexedDependentFunctorSquare.indexed-functor s x))

