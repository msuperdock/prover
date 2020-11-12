module Prover.Category.Dependent.Split.Product where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor)
open import Prover.Category.Dependent.Product
  using (dependent-category-product; dependent-functor-product)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare)
open import Prover.Category.Split.Product
  using (split-functor-product; split-functor-square-product)
open import Prover.Prelude

-- ## Types

-- ### DependentSplitFunctor

dependent-split-functor-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' D₁' D₂' : DependentCategory C}
  → DependentSplitFunctor C₁' D₁'
  → DependentSplitFunctor C₂' D₂'
  → DependentSplitFunctor
    (dependent-category-product C₁' C₂')
    (dependent-category-product D₁' D₂')

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-product
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁₁' C₂₁' D₁₁' D₂₁' : DependentCategory C₁}
  → {C₁₂' C₂₂' D₁₂' D₂₂' : DependentCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → {F₁' : DependentFunctor C₁₁' C₁₂' F}
  → {F₂' : DependentFunctor C₂₁' C₂₂' F}
  → {G₁' : DependentFunctor D₁₁' D₁₂' F}
  → {G₂' : DependentFunctor D₂₁' D₂₂' F}
  → {H₁₁ : DependentSplitFunctor C₁₁' D₁₁'}
  → {H₁₂ : DependentSplitFunctor C₁₂' D₁₂'}
  → {H₂₁ : DependentSplitFunctor C₂₁' D₂₁'}
  → {H₂₂ : DependentSplitFunctor C₂₂' D₂₂'}
  → DependentSplitFunctorSquare F₁' G₁' H₁₁ H₁₂
  → DependentSplitFunctorSquare F₂' G₂' H₂₁ H₂₂
  → DependentSplitFunctorSquare
    (dependent-functor-product F₁' F₂')
    (dependent-functor-product G₁' G₂')
    (dependent-split-functor-product H₁₁ H₂₁)
    (dependent-split-functor-product H₁₂ H₂₂)

-- ## Definitions

-- ### DependentSplitFunctor

dependent-split-functor-product {n = zero} F₁ F₂
  = split-functor-product F₁ F₂

dependent-split-functor-product {n = suc _} F₁ F₂
  = record
  { split-functor
    = λ x → dependent-split-functor-product
      (DependentSplitFunctor.split-functor F₁ x)
      (DependentSplitFunctor.split-functor F₂ x)
  ; split-functor-square
    = λ f → dependent-split-functor-square-product
      (DependentSplitFunctor.split-functor-square F₁ f)
      (DependentSplitFunctor.split-functor-square F₂ f)
  }

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-product {n = zero} s₁ s₂
  = split-functor-square-product s₁ s₂

dependent-split-functor-square-product {n = suc _} s₁ s₂
  = record
  { split-functor
    = λ x₁ → dependent-split-functor-square-product
      (DependentSplitFunctorSquare.split-functor s₁ x₁)
      (DependentSplitFunctorSquare.split-functor s₂ x₁)
  }

