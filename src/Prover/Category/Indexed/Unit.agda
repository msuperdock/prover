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
  using (IndexedSimpleDependentFunctor; IndexedSimpleDependentFunctorCompose;
    IndexedSimpleDependentFunctorIdentity; IndexedSimpleDependentFunctorSquare;
    IndexedSimpleDependentCategory; IndexedSimpleFunctor;
    IndexedSimpleFunctorCompose; IndexedSimpleFunctorIdentity;
    IndexedSimpleFunctorSquare; IndexedSimpleCategory; indexed-function₀;
    indexed-function-compose₀; indexed-function-identity₀;
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

-- ### IndexedDependentCategory

indexed-dependent-category-unit
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → IndexedSimpleDependentCategory C'
  → IndexedDependentCategory C'

-- ### IndexedDependentFunctor

indexed-dependent-functor-unit
  : {n : ℕ}
  → {C D : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {C'' : IndexedSimpleDependentCategory C'}
  → {D'' : IndexedSimpleDependentCategory D'}
  → {F : ChainDependentFunctor C' D'}
  → IndexedSimpleDependentFunctor C'' D'' F
  → IndexedDependentFunctor
    (indexed-dependent-category-unit C'')
    (indexed-dependent-category-unit D'') F

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-unit
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C'' : IndexedSimpleDependentCategory C'}
  → {F : ChainDependentFunctor C' C'}
  → {F' : IndexedSimpleDependentFunctor C'' C'' F}
  → IndexedSimpleDependentFunctorIdentity F'
  → IndexedDependentFunctorIdentity
    (indexed-dependent-functor-unit F')

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-unit
  : {n : ℕ}
  → {C D E : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {E' : ChainDependentCategory E n}
  → {C'' : IndexedSimpleDependentCategory C'}
  → {D'' : IndexedSimpleDependentCategory D'}
  → {E'' : IndexedSimpleDependentCategory E'}
  → {F : ChainDependentFunctor D' E'}
  → {G : ChainDependentFunctor C' D'}
  → {H : ChainDependentFunctor C' E'}
  → {F' : IndexedSimpleDependentFunctor D'' E'' F}
  → {G' : IndexedSimpleDependentFunctor C'' D'' G}
  → {H' : IndexedSimpleDependentFunctor C'' E'' H}
  → IndexedSimpleDependentFunctorCompose F' G' H'
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
  → {C₁'' : IndexedSimpleDependentCategory C₁'}
  → {C₂'' : IndexedSimpleDependentCategory C₂'}
  → {D₁'' : IndexedSimpleDependentCategory D₁'}
  → {D₂'' : IndexedSimpleDependentCategory D₂'}
  → {F : ChainDependentFunctor C₁' C₂'}
  → {G : ChainDependentFunctor D₁' D₂'}
  → {H₁ : ChainDependentFunctor C₁' D₁'}
  → {H₂ : ChainDependentFunctor C₂' D₂'}
  → {F' : IndexedSimpleDependentFunctor C₁'' C₂'' F}
  → {G' : IndexedSimpleDependentFunctor D₁'' D₂'' G}
  → {H₁' : IndexedSimpleDependentFunctor C₁'' D₁'' H₁}
  → {H₂' : IndexedSimpleDependentFunctor C₂'' D₂'' H₂}
  → IndexedSimpleDependentFunctorSquare F' G' H₁' H₂'
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
      (IndexedSimpleCategory.unpack C'))

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
      (IndexedSimpleFunctor.unpack F'))

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
      (IndexedSimpleFunctorIdentity.unpack p))

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
      (IndexedSimpleFunctorCompose.unpack p))

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
      (IndexedSimpleFunctorSquare.unpack s))

indexed-functor-square-unit-eq _ _ refl
  = indexed-functor-square-unit

-- ### IndexedDependentCategory

indexed-dependent-category-unit C''
  = indexed-dependent-category
    (λ x → indexed-category-unit
      (IndexedSimpleDependentCategory.indexed-set C'' x))
    (λ f → indexed-functor-unit
      (IndexedSimpleDependentCategory.indexed-function C'' f))
    (λ x → indexed-functor-identity-unit
      (IndexedSimpleDependentCategory.indexed-function-identity C'' x)) 
    (λ f g → indexed-functor-compose-unit
      (IndexedSimpleDependentCategory.indexed-function-compose C'' f g))

-- ### IndexedDependentFunctor

indexed-dependent-functor-unit F'
  = indexed-dependent-functor
    (λ x → indexed-functor-unit
      (IndexedSimpleDependentFunctor.indexed-function F' x))
    (λ f → indexed-functor-square-unit
      (IndexedSimpleDependentFunctor.indexed-function-square F' f))

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-unit {C' = C'} {C'' = C''} p
  = indexed-dependent-functor-identity
    (IndexedSimpleDependentFunctorIdentity.functor p)
    (λ x → indexed-functor-identity-unit-eq
      (ChainDependentCategory.chain-category C')
      (IndexedSimpleDependentCategory.indexed-set C'')
      (IndexedSimpleDependentFunctorIdentity.base p x)
      (IndexedSimpleDependentFunctorIdentity.indexed-function p x))

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-unit {E' = E'} {E'' = E''} p
  = indexed-dependent-functor-compose
    (IndexedSimpleDependentFunctorCompose.functor p)
    (λ x → indexed-functor-compose-unit-eq
      (ChainDependentCategory.chain-category E')
      (IndexedSimpleDependentCategory.indexed-set E'')
      (IndexedSimpleDependentFunctorCompose.base p x)
      (IndexedSimpleDependentFunctorCompose.indexed-function p x))

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-unit {D₂' = D₂'} {D₂'' = D₂''} s
  = indexed-dependent-functor-square
    (IndexedSimpleDependentFunctorSquare.functor s)
    (λ x₁ → indexed-functor-square-unit-eq
      (ChainDependentCategory.chain-category D₂')
      (IndexedSimpleDependentCategory.indexed-set D₂'')
      (IndexedSimpleDependentFunctorSquare.base s x₁)
      (IndexedSimpleDependentFunctorSquare.indexed-function s x₁))

