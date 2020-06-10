module Prover.Category.Indexed.Unit where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedDependentFunctorCompose; IndexedDependentFunctorIdentity;
    IndexedDependentFunctorSquare; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; empty;
    indexed-dependent-category; indexed-dependent-functor;
    indexed-dependent-functor-compose; indexed-dependent-functor-identity;
    indexed-dependent-functor-square; sigma)
open import Prover.Category.Indexed.Simple
  using (IndexedDependentFunction; IndexedDependentFunctionCompose;
    IndexedDependentFunctionIdentity; IndexedDependentFunctionSquare;
    IndexedDependentSet; IndexedFunction; IndexedFunctionCompose;
    IndexedFunctionIdentity; IndexedFunctionSquare; IndexedSet;
    indexed-function₀; indexed-function-compose₀; indexed-function-identity₀;
    indexed-function-square₀; indexed-set₀)
open import Prover.Category.Unit
  using (category-unit; functor-compose-unit; functor-identity-unit;
    functor-square-unit; functor-unit)
open import Prover.Prelude

-- ## Types

-- ### IndexedCategory

indexed-category-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSet C
  → IndexedCategory C

-- ### IndexedFunctor

indexed-functor-unit
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : IndexedSet C}
  → {D' : IndexedSet D}
  → {F : ChainFunctor C D}
  → IndexedFunction C' D' F
  → IndexedFunctor
    (indexed-category-unit C')
    (indexed-category-unit D') F

-- ### IndexedFunctorIdentity

indexed-functor-identity-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedSet C}
  → {F : ChainFunctor C C}
  → {F' : IndexedFunction C' C' F}
  → IndexedFunctionIdentity F'
  → IndexedFunctorIdentity
    (indexed-functor-unit F')

indexed-functor-identity-unit-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → IndexedSet (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : IndexedFunction (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → IndexedFunctionIdentity F'
  → IndexedFunctorIdentity
    (indexed-functor-unit F')

-- ### IndexedFunctorCompose

indexed-functor-compose-unit
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : IndexedSet C}
  → {D' : IndexedSet D}
  → {E' : IndexedSet E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : IndexedFunction D' E' F}
  → {G' : IndexedFunction C' D' G}
  → {H' : IndexedFunction C' E' H}
  → IndexedFunctionCompose F' G' H'
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
  → {C' : IndexedSet C}
  → {D' : IndexedSet D}
  → (E' : (x : A) → IndexedSet (E x))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F' : IndexedFunction D' (E' x₁) F}
  → {G' : IndexedFunction C' D' G}
  → {H' : IndexedFunction C' (E' x₂) H}
  → x₂ ≡ x₁
  → IndexedFunctionCompose F' G' H'
  → IndexedFunctorCompose
    (indexed-functor-unit F')
    (indexed-functor-unit G')
    (indexed-functor-unit H')

-- ### IndexedFunctorSquare

indexed-functor-square-unit
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : IndexedSet C₁}
  → {C₂' : IndexedSet C₂}
  → {D₁' : IndexedSet D₁}
  → {D₂' : IndexedSet D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : IndexedFunction C₁' C₂' F}
  → {G' : IndexedFunction D₁' D₂' G}
  → {H₁' : IndexedFunction C₁' D₁' H₁}
  → {H₂' : IndexedFunction C₂' D₂' H₂}
  → IndexedFunctionSquare F' G' H₁' H₂'
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
  → {C₁' : IndexedSet C₁}
  → {C₂' : IndexedSet C₂}
  → {D₁' : IndexedSet D₁}
  → (D₂' : (x : A) → IndexedSet (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F' : IndexedFunction C₁' C₂' F}
  → {G' : IndexedFunction D₁' (D₂' x₁) G}
  → {H₁' : IndexedFunction C₁' D₁' H₁}
  → {H₂' : IndexedFunction C₂' (D₂' x₂) H₂}
  → x₂ ≡ x₁
  → IndexedFunctionSquare F' G' H₁' H₂'
  → IndexedFunctorSquare
    (indexed-functor-unit F')
    (indexed-functor-unit G')
    (indexed-functor-unit H₁')
    (indexed-functor-unit H₂')

-- ### IndexedDependentCategory

indexed-dependent-category-unit
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → IndexedDependentSet C'
  → IndexedDependentCategory C'

-- ### IndexedDependentFunctor

indexed-dependent-functor-unit
  : {n : ℕ}
  → {C D : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {C'' : IndexedDependentSet C'}
  → {D'' : IndexedDependentSet D'}
  → {F : ChainDependentFunctor C' D'}
  → IndexedDependentFunction C'' D'' F
  → IndexedDependentFunctor
    (indexed-dependent-category-unit C'')
    (indexed-dependent-category-unit D'') F

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-unit
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C'' : IndexedDependentSet C'}
  → {F : ChainDependentFunctor C' C'}
  → {F' : IndexedDependentFunction C'' C'' F}
  → IndexedDependentFunctionIdentity F'
  → IndexedDependentFunctorIdentity
    (indexed-dependent-functor-unit F')

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-unit
  : {n : ℕ}
  → {C D E : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {E' : ChainDependentCategory E n}
  → {C'' : IndexedDependentSet C'}
  → {D'' : IndexedDependentSet D'}
  → {E'' : IndexedDependentSet E'}
  → {F : ChainDependentFunctor D' E'}
  → {G : ChainDependentFunctor C' D'}
  → {H : ChainDependentFunctor C' E'}
  → {F' : IndexedDependentFunction D'' E'' F}
  → {G' : IndexedDependentFunction C'' D'' G}
  → {H' : IndexedDependentFunction C'' E'' H}
  → IndexedDependentFunctionCompose F' G' H'
  → IndexedDependentFunctorCompose
    (indexed-dependent-functor-unit F')
    (indexed-dependent-functor-unit G')
    (indexed-dependent-functor-unit H')

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-unit
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : Category}
  → {C₁' : ChainDependentCategory C₁ n}
  → {C₂' : ChainDependentCategory C₂ n}
  → {D₁' : ChainDependentCategory D₁ n}
  → {D₂' : ChainDependentCategory D₂ n}
  → {C₁'' : IndexedDependentSet C₁'}
  → {C₂'' : IndexedDependentSet C₂'}
  → {D₁'' : IndexedDependentSet D₁'}
  → {D₂'' : IndexedDependentSet D₂'}
  → {F : ChainDependentFunctor C₁' C₂'}
  → {G : ChainDependentFunctor D₁' D₂'}
  → {H₁ : ChainDependentFunctor C₁' D₁'}
  → {H₂ : ChainDependentFunctor C₂' D₂'}
  → {F' : IndexedDependentFunction C₁'' C₂'' F}
  → {G' : IndexedDependentFunction D₁'' D₂'' G}
  → {H₁' : IndexedDependentFunction C₁'' D₁'' H₁}
  → {H₂' : IndexedDependentFunction C₂'' D₂'' H₂}
  → IndexedDependentFunctionSquare F' G' H₁' H₂'
  → IndexedDependentFunctorSquare
    (indexed-dependent-functor-unit F')
    (indexed-dependent-functor-unit G')
    (indexed-dependent-functor-unit H₁')
    (indexed-dependent-functor-unit H₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-unit
  {n = zero} C'
  = empty
    (category-unit
      (indexed-set₀ C'))
indexed-category-unit
  {n = suc _} C'
  = sigma
    (indexed-dependent-category-unit
      (IndexedSet.unpack C'))

-- ### IndexedFunctor

indexed-functor-unit
  {n = zero} F'
  = empty
    (functor-unit
      (indexed-function₀ F'))
indexed-functor-unit
  {n = suc _} F'
  = sigma
    (indexed-dependent-functor-unit
      (IndexedFunction.unpack F'))

-- ### IndexedFunctorIdentity

indexed-functor-identity-unit
  {n = zero} {F' = F'} p
  = empty
    (functor-identity-unit
      (indexed-function₀ F')
      (indexed-function-identity₀ p))
indexed-functor-identity-unit
  {n = suc _} p
  = sigma
    (indexed-dependent-functor-identity-unit
      (IndexedFunctionIdentity.unpack p))

indexed-functor-identity-unit-eq _ _ refl
  = indexed-functor-identity-unit

-- ### IndexedFunctorCompose

indexed-functor-compose-unit
  {n = zero} {F' = F'} {G' = G'} {H' = H'} p
  = empty
    (functor-compose-unit
      (indexed-function₀ F')
      (indexed-function₀ G')
      (indexed-function₀ H')
      (indexed-function-compose₀ p))
indexed-functor-compose-unit
  {n = suc _} p
  = sigma
    (indexed-dependent-functor-compose-unit
      (IndexedFunctionCompose.unpack p))

indexed-functor-compose-unit-eq _ _ refl
  = indexed-functor-compose-unit

-- ### IndexedFunctorSquare

indexed-functor-square-unit
  {n = zero} {F' = F'} {G' = G'} {H₁' = H₁'} {H₂' = H₂'} s
  = empty
    (functor-square-unit
      (indexed-function₀ F')
      (indexed-function₀ G')
      (indexed-function₀ H₁')
      (indexed-function₀ H₂')
      (indexed-function-square₀ s))
indexed-functor-square-unit
  {n = suc _} s
  = sigma
    (indexed-dependent-functor-square-unit
      (IndexedFunctionSquare.unpack s))

indexed-functor-square-unit-eq _ _ refl
  = indexed-functor-square-unit

-- ### IndexedDependentCategory

indexed-dependent-category-unit C''
  = indexed-dependent-category
    (λ x → indexed-category-unit
      (IndexedDependentSet.indexed-set C'' x))
    (λ f → indexed-functor-unit
      (IndexedDependentSet.indexed-function C'' f))
    (λ x → indexed-functor-identity-unit
      (IndexedDependentSet.indexed-function-identity C'' x)) 
    (λ f g → indexed-functor-compose-unit
      (IndexedDependentSet.indexed-function-compose C'' f g))

-- ### IndexedDependentFunctor

indexed-dependent-functor-unit F'
  = indexed-dependent-functor
    (λ x → indexed-functor-unit
      (IndexedDependentFunction.indexed-function F' x))
    (λ f → indexed-functor-square-unit
      (IndexedDependentFunction.indexed-function-square F' f))

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-unit {C' = C'} {C'' = C''} p
  = indexed-dependent-functor-identity
    (IndexedDependentFunctionIdentity.functor p)
    (λ x → indexed-functor-identity-unit-eq
      (ChainDependentCategory.chain-category C')
      (IndexedDependentSet.indexed-set C'')
      (IndexedDependentFunctionIdentity.base p x)
      (IndexedDependentFunctionIdentity.indexed-function p x))

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-unit {E' = E'} {E'' = E''} p
  = indexed-dependent-functor-compose
    (IndexedDependentFunctionCompose.functor p)
    (λ x → indexed-functor-compose-unit-eq
      (ChainDependentCategory.chain-category E')
      (IndexedDependentSet.indexed-set E'')
      (IndexedDependentFunctionCompose.base p x)
      (IndexedDependentFunctionCompose.indexed-function p x))

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-unit {D₂' = D₂'} {D₂'' = D₂''} s
  = indexed-dependent-functor-square
    (IndexedDependentFunctionSquare.functor s)
    (λ x₁ → indexed-functor-square-unit-eq
      (ChainDependentCategory.chain-category D₂')
      (IndexedDependentSet.indexed-set D₂'')
      (IndexedDependentFunctionSquare.base s x₁)
      (IndexedDependentFunctionSquare.indexed-function s x₁))

