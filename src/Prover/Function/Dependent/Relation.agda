module Prover.Function.Dependent.Relation where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; dependent-category₀;
    dependent-functor₀)
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

  -- #### DependentInjective

  data DependentInjective
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

  dependent-relation-dependent-injective
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → (R : DependentRelation C')
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → DependentInjective
      (dependent-relation-tail R x)
      (dependent-relation-tail R y)
      (DependentCategory.dependent-functor C' f)

  -- #### DependentInjective

  dependent-injective₀
    : {C D : ChainCategory zero}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {R : DependentRelation C'}
    → {S : DependentRelation D'}
    → {F : ChainFunctor C D}
    → {F' : DependentFunctor C' D' F}
    → DependentInjective R S F'
    → Injective
      (dependent-relation₀ R)
      (dependent-relation₀ S)
      (Functor.base (dependent-functor₀ F'))

  dependent-injective-tail
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {R : DependentRelation C'}
    → {S : DependentRelation D'}
    → {F : ChainFunctor C D}
    → {F' : DependentFunctor C' D' F}
    → DependentInjective R S F'
    → (x : ChainCategory.Object C)
    → DependentInjective
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
        → DependentInjective (R x) (R y)
          (DependentCategory.dependent-functor C' f))
      → DependentRelation C'

  dependent-relation₀ (nil R)
    = R

  dependent-relation-tail (cons R _)
    = R

  dependent-relation-dependent-injective (cons _ i)
    = i

  -- #### DependentInjective

  data DependentInjective where

    nil
      : {C D : ChainCategory zero}
      → {C' : DependentCategory C}
      → {D' : DependentCategory D}
      → {R : DependentRelation C'}
      → {S : DependentRelation D'}
      → {F : ChainFunctor C D}
      → {F' : DependentFunctor C' D' F}
      → Injective
        (dependent-relation₀ R)
        (dependent-relation₀ S)
        (Functor.base (dependent-functor₀ F'))
      → DependentInjective R S F'

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
        → DependentInjective
          (dependent-relation-tail R x)
          (dependent-relation-tail S (ChainFunctor.base F x))
          (DependentFunctor.tail F' x))
      → DependentInjective R S F'

  dependent-injective₀ (nil i)
    = i

  dependent-injective-tail (cons i)
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
    ( dependent-relation-dependent-injective
      to dependent-injective
    ; dependent-relation-tail
      to tail
    )

-- ### DependentInjective

DependentInjective
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → DependentRelation C'
  → DependentRelation D'
  → {F : ChainFunctor C D}
  → DependentFunctor C' D' F
  → Set
DependentInjective
  = Internal.DependentInjective

open Internal public
  using (dependent-injective₀)

module DependentInjective where

  open Internal public using () renaming
    ( dependent-injective-tail
      to tail
    )

