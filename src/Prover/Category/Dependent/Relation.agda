module Prover.Category.Dependent.Relation where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor)
open import Prover.Function.Relation
  using (FunctionInjective)
open import Prover.Prelude

-- ## Types

-- ### DependentRelation

DependentRelation
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → Set₁

record DependentRelation'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentCategory C)
  : Set₁

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

record DependentInjective'
  {n : ℕ}
  {C D : ChainCategory (suc n)}
  {C' : DependentCategory C}
  {D' : DependentCategory D}
  (R : DependentRelation C')
  (S : DependentRelation D')
  {F : ChainFunctor C D}
  (F' : DependentFunctor C' D' F)
  : Set

-- ## Definitions

-- ### DependentRelation

DependentRelation {n = zero} C'
  = Relation (Category.Object C')
DependentRelation {n = suc _} C'
  = DependentRelation' C'

record DependentRelation' {_ C} C' where

  inductive

  no-eta-equality

  field

    relation
      : (x : ChainCategory.Object C)
      → DependentRelation
        (DependentCategory.category C' x)

    injective
      : {x y : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C x y)
      → DependentInjective
        (relation x)
        (relation y)
        (DependentCategory.functor C' f)

module DependentRelation
  = DependentRelation'

-- ### DependentInjective

DependentInjective {n = zero} R S F'
  = FunctionInjective R S (Functor.function F')
DependentInjective {n = suc _} R S F'
  = DependentInjective' R S F'

record DependentInjective' {_ C} R S {F} F' where

  inductive

  field

    injective
      : (x : ChainCategory.Object C)
      → DependentInjective
        (DependentRelation.relation R x)
        (DependentRelation.relation S (ChainFunctor.base F x))
        (DependentFunctor.functor F' x)

module DependentInjective
  = DependentInjective'

