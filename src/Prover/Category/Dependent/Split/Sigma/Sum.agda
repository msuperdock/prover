module Prover.Category.Dependent.Split.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; dependent-category₀;
    dependent-category₁; dependent-functor₀; dependent-functor₁)
open import Prover.Category.Dependent.Sigma.Maybe
  using (dependent-category-sigma-maybe; dependent-functor-sigma-maybe)
open import Prover.Category.Dependent.Sigma.Sum
  using (dependent-category-sigma-sum; dependent-functor-sigma-sum)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare; cons;
    dependent-split-functor₀; dependent-split-functor₁;
    dependent-split-functor-square₀; dependent-split-functor-square₁; nil)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-functor-snoc)
open import Prover.Category.Split.Sigma.Sum
  using (split-functor-sigma-sum; split-functor-square-sigma-sum)
open import Prover.Prelude

-- ## Types

-- ### DependentSplitFunctor

dependent-split-functor-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' D₁' : DependentCategory C}
  → {C₂' D₂' : DependentCategory (chain-category-snoc D₁')}
  → (F₁ : DependentSplitFunctor C₁' D₁')
  → DependentSplitFunctor C₂' D₂'
  → DependentSplitFunctor
    (dependent-category-sigma-sum C₂' F₁)
    (dependent-category-sigma-maybe D₁' D₂')

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-sigma-sum
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁₁' D₁₁' : DependentCategory C₁}
  → {C₂₁' D₂₁' : DependentCategory C₂}
  → {C₁₂' D₁₂' : DependentCategory (chain-category-snoc D₁₁')}
  → {C₂₂' D₂₂' : DependentCategory (chain-category-snoc D₂₁')}
  → {F : ChainFunctor C₁ C₂}
  → {F₁' : DependentFunctor C₁₁' C₂₁' F}
  → {G₁' : DependentFunctor D₁₁' D₂₁' F}
  → {F₂' : DependentFunctor C₁₂' C₂₂' (chain-functor-snoc G₁')}
  → {G₂' : DependentFunctor D₁₂' D₂₂' (chain-functor-snoc G₁')}
  → {H₁₁ : DependentSplitFunctor C₁₁' D₁₁'}
  → {H₂₁ : DependentSplitFunctor C₂₁' D₂₁'}
  → {H₁₂ : DependentSplitFunctor C₁₂' D₁₂'}
  → {H₂₂ : DependentSplitFunctor C₂₂' D₂₂'}
  → (s₁ : DependentSplitFunctorSquare F₁' G₁' H₁₁ H₂₁)
  → DependentSplitFunctorSquare F₂' G₂' H₁₂ H₂₂
  → DependentSplitFunctorSquare
    (dependent-functor-sigma-sum F₂' s₁)
    (dependent-functor-sigma-maybe G₁' G₂')
    (dependent-split-functor-sigma-sum H₁₁ H₁₂)
    (dependent-split-functor-sigma-sum H₂₁ H₂₂)

-- ## Definitions

-- ### DependentSplitFunctor

dependent-split-functor-sigma-sum
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'} {C₂' = C₂'} {D₂' = D₂'} F₁ F₂
  = nil
    (split-functor-sigma-sum
      {C₁ = dependent-category₀ C₁'}
      {D₁ = dependent-category₀ D₁'}
      {C₂ = dependent-category₁ C₂'}
      {D₂ = dependent-category₁ D₂'}
      (dependent-split-functor₀ F₁)
      (dependent-split-functor₁ F₂))
dependent-split-functor-sigma-sum
  {n = suc _} F₁ F₂
  = cons
    (λ x → dependent-split-functor-sigma-sum
      (DependentSplitFunctor.tail F₁ x)
      (DependentSplitFunctor.tail F₂ x))
    (λ f → dependent-split-functor-square-sigma-sum
      (DependentSplitFunctor.dependent-split-functor-square F₁ f)
      (DependentSplitFunctor.dependent-split-functor-square F₂ f))

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {D₁₁' = D₁₁'} {C₂₁' = C₂₁'} {D₂₁' = D₂₁'}
  {C₁₂' = C₁₂'} {D₁₂' = D₁₂'} {C₂₂' = C₂₂'} {D₂₂' = D₂₂'}
  {F₁' = F₁'} {F₂' = F₂'} {G₂' = G₂'}
  {H₁₁ = H₁₁} {H₂₁ = H₂₁} {H₁₂ = H₁₂} {H₂₂ = H₂₂} s₁ s₂
  = nil
    (split-functor-square-sigma-sum
      {C₁₁ = dependent-category₀ C₁₁'}
      {C₂₁ = dependent-category₀ C₂₁'}
      {D₁₁ = dependent-category₀ D₁₁'}
      {D₂₁ = dependent-category₀ D₂₁'}
      {C₁₂ = dependent-category₁ C₁₂'}
      {D₁₂ = dependent-category₁ D₁₂'}
      {C₂₂ = dependent-category₁ C₂₂'}
      {D₂₂ = dependent-category₁ D₂₂'}
      {F₁ = dependent-functor₀ F₁'}
      {F₂ = dependent-functor₁ F₂'}
      {G₂ = dependent-functor₁ G₂'}
      {H₁₁ = dependent-split-functor₀ H₁₁}
      {H₂₁ = dependent-split-functor₀ H₂₁}
      {H₁₂ = dependent-split-functor₁ H₁₂}
      {H₂₂ = dependent-split-functor₁ H₂₂}
      (dependent-split-functor-square₀ s₁)
      (dependent-split-functor-square₁ s₂))
dependent-split-functor-square-sigma-sum
  {n = suc _} s₁ s₂
  = cons
    (λ x₁ → dependent-split-functor-square-sigma-sum
      (DependentSplitFunctorSquare.tail s₁ x₁)
      (DependentSplitFunctorSquare.tail s₂ x₁))

