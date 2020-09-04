module Prover.Category.Dependent.Split.Product where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor)
open import Prover.Category.Dependent.Product
  using (dependent-category-product; dependent-functor-product)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare; cons;
    dependent-split-functor₀; dependent-split-functor-square₀; nil)
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
  → {C₁₁' C₁₂' D₁₁' D₁₂' : DependentCategory C₁}
  → {C₂₁' C₂₂' D₂₁' D₂₂' : DependentCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → {F₁' : DependentFunctor C₁₁' C₂₁' F}
  → {F₂' : DependentFunctor C₁₂' C₂₂' F}
  → {G₁' : DependentFunctor D₁₁' D₂₁' F}
  → {G₂' : DependentFunctor D₁₂' D₂₂' F}
  → {H₁₁ : DependentSplitFunctor C₁₁' D₁₁'}
  → {H₁₂ : DependentSplitFunctor C₁₂' D₁₂'}
  → {H₂₁ : DependentSplitFunctor C₂₁' D₂₁'}
  → {H₂₂ : DependentSplitFunctor C₂₂' D₂₂'}
  → DependentSplitFunctorSquare F₁' G₁' H₁₁ H₂₁
  → DependentSplitFunctorSquare F₂' G₂' H₁₂ H₂₂
  → DependentSplitFunctorSquare
    (dependent-functor-product F₁' F₂')
    (dependent-functor-product G₁' G₂')
    (dependent-split-functor-product H₁₁ H₁₂)
    (dependent-split-functor-product H₂₁ H₂₂)

-- ## Definitions

-- ### DependentSplitFunctor

dependent-split-functor-product
  {n = zero} F₁ F₂
  = nil
    (split-functor-product
      (dependent-split-functor₀ F₁)
      (dependent-split-functor₀ F₂))
dependent-split-functor-product
  {n = suc _} F₁ F₂
  = cons
    (λ x → dependent-split-functor-product
      (DependentSplitFunctor.tail F₁ x)
      (DependentSplitFunctor.tail F₂ x))
    (λ f → dependent-split-functor-square-product
      (DependentSplitFunctor.dependent-split-functor-square F₁ f)
      (DependentSplitFunctor.dependent-split-functor-square F₂ f))

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-product
  {n = zero} s₁ s₂
  = nil
    (split-functor-square-product
      (dependent-split-functor-square₀ s₁)
      (dependent-split-functor-square₀ s₂))
dependent-split-functor-square-product
  {n = suc _} s₁ s₂
  = cons
    (λ x₁ → dependent-split-functor-square-product
      (DependentSplitFunctorSquare.tail s₁ x₁)
      (DependentSplitFunctorSquare.tail s₂ x₁))

