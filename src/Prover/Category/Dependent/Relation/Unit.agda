module Prover.Category.Dependent.Relation.Unit where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent.Relation
  using (DependentRelation; DependentInjective)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; DependentSimpleFunctor)
open import Prover.Category.Dependent.Simple.Relation
  using (DependentSimpleRelation; DependentSimpleInjective)
open import Prover.Category.Dependent.Unit
  using (dependent-category-unit; dependent-functor-unit)
open import Prover.Prelude

-- ## Types

-- ### DependentRelation

dependent-relation-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleRelation C'
  → DependentRelation
    (dependent-category-unit C')

-- ### DependentInjective

dependent-injective-unit
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {R : DependentSimpleRelation C'}
  → {S : DependentSimpleRelation D'}
  → {F : ChainFunctor C D}
  → {F' : DependentSimpleFunctor C' D' F}
  → DependentSimpleInjective R S F'
  → DependentInjective
    (dependent-relation-unit R)
    (dependent-relation-unit S)
    (dependent-functor-unit F')

-- ## Definitions

-- ### DependentRelation

dependent-relation-unit {n = zero} R
  = R

dependent-relation-unit {n = suc _} R
  = record
  { relation
    = λ x → dependent-relation-unit
      (DependentSimpleRelation.relation R x)
  ; injective
    = λ f → dependent-injective-unit
      (DependentSimpleRelation.injective R f)
  }

-- ### DependentInjective

dependent-injective-unit {n = zero} i
  = i

dependent-injective-unit {n = suc _} i
  = record
  { injective
    = λ x → dependent-injective-unit
      (DependentSimpleInjective.injective i x)
  }

