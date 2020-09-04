module Prover.Category.Dependent.Split.List where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor)
open import Prover.Category.Dependent.List
  using (dependent-category-list; dependent-functor-list)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare; cons;
    dependent-split-functor₀; dependent-split-functor-square₀; nil)
open import Prover.Category.Split.List
  using (split-functor-list; split-functor-square-list)
open import Prover.Prelude

-- ## Types

-- ### DependentSplitFunctor

dependent-split-functor-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → DependentSplitFunctor C' D'
  → DependentSplitFunctor
    (dependent-category-list C')
    (dependent-category-list D')

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-list
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' D₁' : DependentCategory C₁}
  → {C₂' D₂' : DependentCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' D₂' F}
  → {H₁ : DependentSplitFunctor C₁' D₁'}
  → {H₂ : DependentSplitFunctor C₂' D₂'}
  → DependentSplitFunctorSquare F' G' H₁ H₂
  → DependentSplitFunctorSquare
    (dependent-functor-list F')
    (dependent-functor-list G')
    (dependent-split-functor-list H₁)
    (dependent-split-functor-list H₂)

-- ## Definitions

-- ### DependentSplitFunctor

dependent-split-functor-list
  {n = zero} F
  = nil
    (split-functor-list
      (dependent-split-functor₀ F))
dependent-split-functor-list
  {n = suc _} F
  = cons
    (λ x → dependent-split-functor-list
      (DependentSplitFunctor.tail F x))
    (λ f → dependent-split-functor-square-list
      (DependentSplitFunctor.dependent-split-functor-square F f))

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-list
  {n = zero} s
  = nil
    (split-functor-square-list
      (dependent-split-functor-square₀ s))
dependent-split-functor-square-list
  {n = suc _} s
  = cons
    (λ x₁ → dependent-split-functor-square-list
      (DependentSplitFunctorSquare.tail s x₁))

