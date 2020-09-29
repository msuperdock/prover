module Prover.Category.Dependent.Split.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor)
open import Prover.Category.Dependent.Sigma.Maybe
  using (dependent-category-sigma-maybe; dependent-functor-sigma-maybe)
open import Prover.Category.Dependent.Sigma.Sum
  using (dependent-category-sigma-sum; dependent-functor-sigma-sum)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare)
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

dependent-split-functor-sigma-sum {n = zero} F₁ F₂
  = split-functor-sigma-sum F₁ F₂

dependent-split-functor-sigma-sum {n = suc _} F₁ F₂
  = record
  { split-functor
    = λ x → dependent-split-functor-sigma-sum
      (DependentSplitFunctor.split-functor F₁ x)
      (DependentSplitFunctor.split-functor F₂ x)
  ; split-functor-square
    = λ f → dependent-split-functor-square-sigma-sum
      (DependentSplitFunctor.split-functor-square F₁ f)
      (DependentSplitFunctor.split-functor-square F₂ f)
  }

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-sigma-sum {n = zero} s₁ s₂
  = split-functor-square-sigma-sum s₁ s₂

dependent-split-functor-square-sigma-sum {n = suc _} s₁ s₂
  = record
  { split-functor
    = λ x₁ → dependent-split-functor-square-sigma-sum
      (DependentSplitFunctorSquare.split-functor s₁ x₁)
      (DependentSplitFunctorSquare.split-functor s₂ x₁)
  }

