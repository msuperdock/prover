module Prover.Category.Dependent.Split.List.Unit where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent.List
  using (dependent-category-list; dependent-functor-list)
open import Prover.Category.Dependent.List.Unit
  using (dependent-category-list-unit; dependent-functor-list-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; DependentSimpleFunctor)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare)
open import Prover.Category.Dependent.Unit
  using (dependent-category-unit; dependent-functor-unit)
open import Prover.Category.Split.List.Unit
  using (split-functor-list-unit; split-functor-square-list-unit)
open import Prover.Prelude

-- ## Types

-- ### DependentSplitFunctor

dependent-split-functor-list-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C' : DependentSimpleCategory C)
  → DependentSplitFunctor
    (dependent-category-list (dependent-category-unit C'))
    (dependent-category-list-unit C')

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-list-unit
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → (F' : DependentSimpleFunctor C₁' C₂' F)
  → DependentSplitFunctorSquare
    (dependent-functor-list (dependent-functor-unit F'))
    (dependent-functor-list-unit F')
    (dependent-split-functor-list-unit C₁')
    (dependent-split-functor-list-unit C₂')

-- ## Definitions

-- ### DependentSplitFunctor

dependent-split-functor-list-unit {n = zero} C'
  = split-functor-list-unit C'

dependent-split-functor-list-unit {n = suc _} C'
  = record
  { split-functor
    = λ x → dependent-split-functor-list-unit
      (DependentSimpleCategory.category C' x)
  ; split-functor-square
    = λ f → dependent-split-functor-square-list-unit
      (DependentSimpleCategory.functor C' f)
  }

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-list-unit {n = zero} F'
  = split-functor-square-list-unit F'

dependent-split-functor-square-list-unit {n = suc _} F'
  = record
  { split-functor
    = λ x₁ → dependent-split-functor-square-list-unit
      (DependentSimpleFunctor.functor F' x₁)
  }

