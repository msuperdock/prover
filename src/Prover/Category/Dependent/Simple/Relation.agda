module Prover.Category.Dependent.Simple.Relation where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; DependentSimpleFunctor)
open import Prover.Function.Relation
  using (FunctionInjective)
open import Prover.Prelude

-- ## Types

-- ### DependentSimpleRelation

DependentSimpleRelation
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → Set₁

record DependentSimpleRelation'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleCategory C)
  : Set₁

-- ### DependentSimpleInjective

DependentSimpleInjective
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → DependentSimpleRelation C'
  → DependentSimpleRelation D'
  → {F : ChainFunctor C D}
  → DependentSimpleFunctor C' D' F
  → Set

record DependentSimpleInjective'
  {n : ℕ}
  {C D : ChainCategory (suc n)}
  {C' : DependentSimpleCategory C}
  {D' : DependentSimpleCategory D}
  (R : DependentSimpleRelation C')
  (S : DependentSimpleRelation D')
  {F : ChainFunctor C D}
  (F' : DependentSimpleFunctor C' D' F)
  : Set

-- ## Definitions

-- ### DependentSimpleRelation

DependentSimpleRelation {n = zero} C'
  = Relation C'
DependentSimpleRelation {n = suc _} C'
  = DependentSimpleRelation' C'

record DependentSimpleRelation' {_ C} C' where

  inductive

  no-eta-equality

  field

    relation
      : (x : ChainCategory.Object C)
      → DependentSimpleRelation
        (DependentSimpleCategory.category C' x)

    injective
      : {x y : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C x y)
      → DependentSimpleInjective
        (relation x)
        (relation y)
        (DependentSimpleCategory.functor C' f)

module DependentSimpleRelation
  = DependentSimpleRelation'

-- ### DependentSimpleInjective

DependentSimpleInjective {n = zero} R S
  = FunctionInjective R S
DependentSimpleInjective {n = suc _} R S
  = DependentSimpleInjective' R S

record DependentSimpleInjective' {_ C} R S {F} F' where

  inductive

  field

    injective
      : (x : ChainCategory.Object C)
      → DependentSimpleInjective
        (DependentSimpleRelation.relation R x)
        (DependentSimpleRelation.relation S (ChainFunctor.base F x))
        (DependentSimpleFunctor.functor F' x)

module DependentSimpleInjective
  = DependentSimpleInjective'

