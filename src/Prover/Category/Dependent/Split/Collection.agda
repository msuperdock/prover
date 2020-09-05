module Prover.Category.Dependent.Split.Collection where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; dependent-category₀;
    dependent-functor₀)
open import Prover.Category.Dependent.Collection
  using (dependent-category-collection; dependent-functor-collection)
open import Prover.Category.Dependent.List
  using (dependent-category-list; dependent-functor-list)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare; cons; nil)
open import Prover.Category.Split.Collection
  using (split-functor-collection; split-functor-square-collection)
open import Prover.Function.Dependent.Decidable
  using (DependentDecidable; dependent-decidable₀)
open import Prover.Function.Dependent.Relation
  using (DependentInjective; DependentRelation; dependent-injective₀;
    dependent-relation₀)
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

dependent-split-functor-collection
  {n = zero} {C' = C'} {R = R} d
  = nil
    (split-functor-collection
      (dependent-category₀ C')
      (dependent-relation₀ R)
      (dependent-decidable₀ d))
dependent-split-functor-collection
  {n = suc _} {R = R} d
  = cons
    (λ x → dependent-split-functor-collection
      (DependentDecidable.tail d x))
    (λ {x = x} {y = y} f → dependent-split-functor-square-collection
      (DependentDecidable.tail d x)
      (DependentDecidable.tail d y)
      (DependentRelation.dependent-injective R f))

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-collection
  {n = zero} {R₁ = R₁} {R₂ = R₂} d₁ d₂ {F' = F'} i
  = nil
    (split-functor-square-collection
      (dependent-relation₀ R₁)
      (dependent-relation₀ R₂)
      (dependent-decidable₀ d₁)
      (dependent-decidable₀ d₂)
      (dependent-functor₀ F')
      (dependent-injective₀ i))
dependent-split-functor-square-collection
  {n = suc _} d₁ d₂ {F = F} i
  = cons
    (λ x₁ → dependent-split-functor-square-collection
      (DependentDecidable.tail d₁ x₁)
      (DependentDecidable.tail d₂ (ChainFunctor.base F x₁))
      (DependentInjective.tail i x₁))

