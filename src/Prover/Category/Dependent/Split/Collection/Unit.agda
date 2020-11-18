module Prover.Category.Dependent.Split.Collection.Unit where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent.Collection.Unit
  using (dependent-category-collection-unit; dependent-functor-collection-unit)
open import Prover.Category.Dependent.List.Unit
  using (dependent-category-list-unit; dependent-functor-list-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; DependentSimpleFunctor)
open import Prover.Category.Dependent.Simple.Decidable
  using (DependentSimpleDecidable)
open import Prover.Category.Dependent.Simple.Relation
  using (DependentSimpleInjective; DependentSimpleRelation)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare)
open import Prover.Category.Split.Collection.Unit
  using (split-functor-collection-unit; split-functor-square-collection-unit)
open import Prover.Prelude

-- ## Types

-- ### DependentSplitFunctor

dependent-split-functor-collection-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → DependentSplitFunctor
    (dependent-category-list-unit C')
    (dependent-category-collection-unit R)

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-collection-unit
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {R₁ : DependentSimpleRelation C₁'}
  → {R₂ : DependentSimpleRelation C₂'}
  → (d₁ : DependentSimpleDecidable R₁)
  → (d₂ : DependentSimpleDecidable R₂)
  → {F : ChainFunctor C₁ C₂}
  → {F' : DependentSimpleFunctor C₁' C₂' F}
  → (i : DependentSimpleInjective R₁ R₂ F')
  → DependentSplitFunctorSquare
    (dependent-functor-list-unit F')
    (dependent-functor-collection-unit i)
    (dependent-split-functor-collection-unit d₁)
    (dependent-split-functor-collection-unit d₂)

-- ## Definitions

-- ### DependentSplitFunctor

dependent-split-functor-collection-unit {n = zero} {R = R} d
  = split-functor-collection-unit R d

dependent-split-functor-collection-unit {n = suc _} {R = R} d
  = record
  { split-functor
    = λ x → dependent-split-functor-collection-unit
      (DependentSimpleDecidable.decidable d x)
  ; split-functor-square
    = λ {x = x} {y = y} f → dependent-split-functor-square-collection-unit
      (DependentSimpleDecidable.decidable d x)
      (DependentSimpleDecidable.decidable d y)
      (DependentSimpleRelation.injective R f)
  }

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-collection-unit {n = zero} d₁ d₂ i
  = split-functor-square-collection-unit d₁ d₂ i

dependent-split-functor-square-collection-unit {n = suc _} d₁ d₂ {F = F} i
  = record
  { split-functor
    = λ x₁ → dependent-split-functor-square-collection-unit
      (DependentSimpleDecidable.decidable d₁ x₁)
      (DependentSimpleDecidable.decidable d₂ (ChainFunctor.base F x₁))
      (DependentSimpleInjective.injective i x₁)
  }

