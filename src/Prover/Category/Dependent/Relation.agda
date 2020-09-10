module Prover.Category.Dependent.Relation where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; dependent-category₀;
    dependent-functor₀)
open import Prover.Function
  using (FunctionInjective)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types

  -- #### DependentRelation

  data DependentRelation
    : {n : ℕ}
    → {C : ChainCategory n}
    → DependentCategory C
    → Set₁

  -- #### DependentFunctorInjective

  data DependentFunctorInjective
    : {n : ℕ}
    → {C D : ChainCategory n}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → DependentRelation C'
    → DependentRelation D'
    → {F : ChainFunctor C D}
    → DependentFunctor C' D' F
    → Set

  -- ### Interface

  -- #### DependentRelation

  dependent-relation₀
    : {C : ChainCategory zero}
    → {C' : DependentCategory C}
    → DependentRelation C'
    → Relation (Category.Object (dependent-category₀ C'))

  dependent-relation-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → DependentRelation C'
    → (x : ChainCategory.Object C)
    → DependentRelation (DependentCategory.tail C' x)

  dependent-relation-dependent-functor-injective
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → (R : DependentRelation C')
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → DependentFunctorInjective
      (dependent-relation-tail R x)
      (dependent-relation-tail R y)
      (DependentCategory.dependent-functor C' f)

  -- #### DependentFunctorInjective

  dependent-functor-injective₀
    : {C D : ChainCategory zero}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {R : DependentRelation C'}
    → {S : DependentRelation D'}
    → {F : ChainFunctor C D}
    → {F' : DependentFunctor C' D' F}
    → DependentFunctorInjective R S F'
    → FunctionInjective
      (dependent-relation₀ R)
      (dependent-relation₀ S)
      (Functor.function (dependent-functor₀ F'))

  dependent-functor-injective-tail
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {R : DependentRelation C'}
    → {S : DependentRelation D'}
    → {F : ChainFunctor C D}
    → {F' : DependentFunctor C' D' F}
    → DependentFunctorInjective R S F'
    → (x : ChainCategory.Object C)
    → DependentFunctorInjective
      (dependent-relation-tail R x)
      (dependent-relation-tail S (ChainFunctor.base F x))
      (DependentFunctor.tail F' x)

  -- ### Definitions

  -- #### DependentRelation

  data DependentRelation where

    nil
      : {C : ChainCategory zero}
      → {C' : DependentCategory C}
      → Relation (Category.Object (dependent-category₀ C'))
      → DependentRelation C'

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : DependentCategory C}
      → (R : (x : ChainCategory.Object C)
        → DependentRelation
          (DependentCategory.tail C' x))
      → ({x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → DependentFunctorInjective (R x) (R y)
          (DependentCategory.dependent-functor C' f))
      → DependentRelation C'

  dependent-relation₀ (nil R)
    = R

  dependent-relation-tail (cons R _)
    = R

  dependent-relation-dependent-functor-injective (cons _ i)
    = i

  -- #### DependentFunctorInjective

  data DependentFunctorInjective where

    nil
      : {C D : ChainCategory zero}
      → {C' : DependentCategory C}
      → {D' : DependentCategory D}
      → {R : DependentRelation C'}
      → {S : DependentRelation D'}
      → {F : ChainFunctor C D}
      → {F' : DependentFunctor C' D' F}
      → FunctionInjective
        (dependent-relation₀ R)
        (dependent-relation₀ S)
        (Functor.function (dependent-functor₀ F'))
      → DependentFunctorInjective R S F'

    cons
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → {C' : DependentCategory C}
      → {D' : DependentCategory D}
      → {R : DependentRelation C'}
      → {S : DependentRelation D'}
      → {F : ChainFunctor C D}
      → {F' : DependentFunctor C' D' F}
      → ((x : ChainCategory.Object C)
        → DependentFunctorInjective
          (dependent-relation-tail R x)
          (dependent-relation-tail S (ChainFunctor.base F x))
          (DependentFunctor.tail F' x))
      → DependentFunctorInjective R S F'

  dependent-functor-injective₀ (nil i)
    = i

  dependent-functor-injective-tail (cons i)
    = i

-- ## Modules

-- ### DependentRelation

DependentRelation
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → Set₁
DependentRelation
  = Internal.DependentRelation

open Internal public
  using (dependent-relation₀)

module DependentRelation where

  open Internal public using () renaming
    ( dependent-relation-dependent-functor-injective
      to dependent-functor-injective
    ; dependent-relation-tail
      to tail
    )

-- ### DependentFunctorInjective

DependentFunctorInjective
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → DependentRelation C'
  → DependentRelation D'
  → {F : ChainFunctor C D}
  → DependentFunctor C' D' F
  → Set
DependentFunctorInjective
  = Internal.DependentFunctorInjective

open Internal public
  using (dependent-functor-injective₀)

module DependentFunctorInjective where

  open Internal public using () renaming
    ( dependent-functor-injective-tail
      to tail
    )

