module Prover.Category.Dependent.Split.Collection where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor)
open import Prover.Category.Dependent.Collection
  using (dependent-category-collection; dependent-functor-collection)
open import Prover.Category.Dependent.Decidable
  using (DependentDecidable)
open import Prover.Category.Dependent.List
  using (dependent-category-list; dependent-functor-list)
open import Prover.Category.Dependent.Relation
  using (DependentInjective; DependentRelation)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare)
open import Prover.Category.Split.Collection
  using (split-functor-collection; split-functor-square-collection)
open import Prover.Prelude

-- ## Types

-- ### DependentSplitFunctor

dependent-split-functor-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → DependentDecidable R
  → DependentSplitFunctor
    (dependent-category-list C')
    (dependent-category-collection R)

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-collection
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {R₁ : DependentRelation C₁'}
  → {R₂ : DependentRelation C₂'}
  → (d₁ : DependentDecidable R₁)
  → (d₂ : DependentDecidable R₂)
  → {F : ChainFunctor C₁ C₂}
  → {F' : DependentFunctor C₁' C₂' F}
  → (i : DependentInjective R₁ R₂ F')
  → DependentSplitFunctorSquare
    (dependent-functor-list F')
    (dependent-functor-collection i)
    (dependent-split-functor-collection d₁)
    (dependent-split-functor-collection d₂)

-- ## Definitions

-- ### DependentSplitFunctor

dependent-split-functor-collection {n = zero} {C' = C'} {R = R} d
  = split-functor-collection C' R d

dependent-split-functor-collection {n = suc _} {R = R} d
  = record
  { split-functor
    = λ x → dependent-split-functor-collection
      (DependentDecidable.decidable d x)
  ; split-functor-square
    = λ {x = x} {y = y} f → dependent-split-functor-square-collection
      (DependentDecidable.decidable d x)
      (DependentDecidable.decidable d y)
      (DependentRelation.injective R f)
  }

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-collection {n = zero} d₁ d₂ {F' = F'} i
  = split-functor-square-collection d₁ d₂ F' i

dependent-split-functor-square-collection {n = suc _} d₁ d₂ {F = F} i
  = record
  { split-functor
    = λ x₁ → dependent-split-functor-square-collection
      (DependentDecidable.decidable d₁ x₁)
      (DependentDecidable.decidable d₂ (ChainFunctor.base F x₁))
      (DependentInjective.injective i x₁)
  }

