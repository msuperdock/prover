module Prover.Category.Indexed.Simple.Convert where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedDependentFunctorCompose; IndexedDependentFunctorIdentity;
    IndexedDependentFunctorSquare; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; indexed-category₀;
    indexed-functor₀; indexed-functor-compose₀; indexed-functor-identity₀;
    indexed-functor-square₀)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleDependentFunctor; IndexedSimpleDependentFunctorCompose;
    IndexedSimpleDependentFunctorIdentity; IndexedSimpleDependentFunctorSquare;
    IndexedSimpleDependentCategory; IndexedSimpleFunctor;
    IndexedSimpleFunctorCompose; IndexedSimpleFunctorIdentity;
    IndexedSimpleFunctorSquare; IndexedSimpleCategory; empty;
    indexed-simple-dependent-functor; indexed-simple-dependent-functor-compose;
    indexed-simple-dependent-functor-identity;
    indexed-simple-dependent-functor-square;
    indexed-simple-dependent-category; sigma)
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

-- ### IndexedDependentCategory

indexed-dependent-category-simple
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → IndexedDependentCategory C'
  → IndexedSimpleDependentCategory C'

-- ### IndexedDependentFunctor

indexed-dependent-functor-simple
  : {n : ℕ}
  → {C D : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {C'' : IndexedDependentCategory C'}
  → {D'' : IndexedDependentCategory D'}
  → {F : ChainDependentFunctor C' D'}
  → IndexedDependentFunctor C'' D'' F
  → IndexedSimpleDependentFunctor
    (indexed-dependent-category-simple C'')
    (indexed-dependent-category-simple D'') F

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-simple
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C'' : IndexedDependentCategory C'}
  → {F : ChainDependentFunctor C' C'}
  → {F' : IndexedDependentFunctor C'' C'' F}
  → IndexedDependentFunctorIdentity F'
  → IndexedSimpleDependentFunctorIdentity
    (indexed-dependent-functor-simple F')

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-simple
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
  → IndexedSimpleDependentFunctorCompose
    (indexed-dependent-functor-simple F')
    (indexed-dependent-functor-simple G')
    (indexed-dependent-functor-simple H')

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-simple
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
  → IndexedSimpleDependentFunctorSquare
    (indexed-dependent-functor-simple F')
    (indexed-dependent-functor-simple G')
    (indexed-dependent-functor-simple H₁')
    (indexed-dependent-functor-simple H₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-simple {n = zero} C'
  = empty
    (Category.Object
      (indexed-category₀ C'))
indexed-category-simple {n = suc _} C'
  = sigma
    (indexed-dependent-category-simple
      (IndexedCategory.unpack C'))

-- ### IndexedFunctor

indexed-functor-simple {n = zero} F'
  = empty
    (Functor.base
      (indexed-functor₀ F'))
indexed-functor-simple {n = suc _} F'
  = sigma
    (indexed-dependent-functor-simple
      (IndexedFunctor.unpack F'))

-- ### IndexedFunctorIdentity

indexed-functor-identity-simple {n = zero} p
  = empty
    (FunctorIdentity.base
      (indexed-functor-identity₀ p))
indexed-functor-identity-simple {n = suc _} p
  = sigma
    (indexed-dependent-functor-identity-simple
      (IndexedFunctorIdentity.unpack p))

indexed-functor-identity-simple-eq _ _ refl
  = indexed-functor-identity-simple

-- ### IndexedFunctorCompose

indexed-functor-compose-simple {n = zero} p
  = empty
    (FunctorCompose.base
      (indexed-functor-compose₀ p))
indexed-functor-compose-simple {n = suc _} p
  = sigma
    (indexed-dependent-functor-compose-simple
      (IndexedFunctorCompose.unpack p))

indexed-functor-compose-simple-eq _ _ refl
  = indexed-functor-compose-simple

-- ### IndexedFunctorSquare

indexed-functor-square-simple {n = zero} s
  = empty
    (FunctorSquare.base
      (indexed-functor-square₀ s))
indexed-functor-square-simple {n = suc _} s
  = sigma
    (indexed-dependent-functor-square-simple
      (IndexedFunctorSquare.unpack s))

indexed-functor-square-simple-eq _ _ refl
  = indexed-functor-square-simple

-- ### IndexedDependentCategory

indexed-dependent-category-simple C''
  = indexed-simple-dependent-category
    (λ x → indexed-category-simple
      (IndexedDependentCategory.indexed-category C'' x))
    (λ f → indexed-functor-simple
      (IndexedDependentCategory.indexed-functor C'' f))
    (λ x → indexed-functor-identity-simple
      (IndexedDependentCategory.indexed-functor-identity C'' x))
    (λ f g → indexed-functor-compose-simple
      (IndexedDependentCategory.indexed-functor-compose C'' f g))

-- ### IndexedDependentFunctor

indexed-dependent-functor-simple F'
  = indexed-simple-dependent-functor
    (λ x → indexed-functor-simple
      (IndexedDependentFunctor.indexed-functor F' x))
    (λ f → indexed-functor-square-simple
      (IndexedDependentFunctor.indexed-functor-square F' f))

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-simple {C' = C'} {C'' = C''} p
  = indexed-simple-dependent-functor-identity
    (IndexedDependentFunctorIdentity.functor p)
    (λ x → indexed-functor-identity-simple-eq
      (ChainDependentCategory.chain-category C')
      (IndexedDependentCategory.indexed-category C'')
      (IndexedDependentFunctorIdentity.base p x)
      (IndexedDependentFunctorIdentity.indexed-functor p x))

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-simple {E' = E'} {E'' = E''} p
  = indexed-simple-dependent-functor-compose
    (IndexedDependentFunctorCompose.functor p)
    (λ x → indexed-functor-compose-simple-eq
      (ChainDependentCategory.chain-category E')
      (IndexedDependentCategory.indexed-category E'')
      (IndexedDependentFunctorCompose.base p x)
      (IndexedDependentFunctorCompose.indexed-functor p x))

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-simple {D₂' = D₂'} {D₂'' = D₂''} s
  = indexed-simple-dependent-functor-square
    (IndexedDependentFunctorSquare.functor s)
    (λ x₁ → indexed-functor-square-simple-eq
      (ChainDependentCategory.chain-category D₂')
      (IndexedDependentCategory.indexed-category D₂'')
      (IndexedDependentFunctorSquare.base s x₁)
      (IndexedDependentFunctorSquare.indexed-functor s x₁))

