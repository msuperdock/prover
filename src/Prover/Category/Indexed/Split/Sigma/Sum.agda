module Prover.Category.Indexed.Split.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor; indexed-category₀; indexed-category₁;
    indexed-functor₀; indexed-functor₁)
open import Prover.Category.Indexed.Sigma.Maybe
  using (indexed-category-sigma-maybe; indexed-functor-sigma-maybe)
open import Prover.Category.Indexed.Sigma.Sum
  using (indexed-category-sigma-sum; indexed-functor-sigma-sum)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor; IndexedSplitFunctorSquare; cons;
    indexed-split-functor₀; indexed-split-functor₁;
    indexed-split-functor-square₀; indexed-split-functor-square₁; nil)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-functor-snoc)
open import Prover.Category.Split.Sigma.Sum
  using (split-functor-sigma-sum; split-functor-square-sigma-sum)
open import Prover.Prelude

-- ## Types

-- ### IndexedSplitFunctor

indexed-split-functor-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' D₁' : IndexedCategory C}
  → {C₂' D₂' : IndexedCategory (chain-category-snoc D₁')}
  → (F₁ : IndexedSplitFunctor C₁' D₁')
  → IndexedSplitFunctor C₂' D₂'
  → IndexedSplitFunctor
    (indexed-category-sigma-sum C₂' F₁)
    (indexed-category-sigma-maybe D₁' D₂')

-- ### IndexedSplitFunctorSquare

indexed-split-functor-square-sigma-sum
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁₁' D₁₁' : IndexedCategory C₁}
  → {C₂₁' D₂₁' : IndexedCategory C₂}
  → {C₁₂' D₁₂' : IndexedCategory (chain-category-snoc D₁₁')}
  → {C₂₂' D₂₂' : IndexedCategory (chain-category-snoc D₂₁')}
  → {F : ChainFunctor C₁ C₂}
  → {F₁' : IndexedFunctor C₁₁' C₂₁' F}
  → {G₁' : IndexedFunctor D₁₁' D₂₁' F}
  → {F₂' : IndexedFunctor C₁₂' C₂₂' (chain-functor-snoc G₁')}
  → {G₂' : IndexedFunctor D₁₂' D₂₂' (chain-functor-snoc G₁')}
  → {H₁₁ : IndexedSplitFunctor C₁₁' D₁₁'}
  → {H₂₁ : IndexedSplitFunctor C₂₁' D₂₁'}
  → {H₁₂ : IndexedSplitFunctor C₁₂' D₁₂'}
  → {H₂₂ : IndexedSplitFunctor C₂₂' D₂₂'}
  → (s₁ : IndexedSplitFunctorSquare F₁' G₁' H₁₁ H₂₁)
  → IndexedSplitFunctorSquare F₂' G₂' H₁₂ H₂₂
  → IndexedSplitFunctorSquare
    (indexed-functor-sigma-sum F₂' s₁)
    (indexed-functor-sigma-maybe G₁' G₂')
    (indexed-split-functor-sigma-sum H₁₁ H₁₂)
    (indexed-split-functor-sigma-sum H₂₁ H₂₂)

-- ## Definitions

-- ### IndexedSplitFunctor

indexed-split-functor-sigma-sum
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'} {C₂' = C₂'} {D₂' = D₂'} F₁ F₂
  = nil
    (split-functor-sigma-sum
      {C₁ = indexed-category₀ C₁'}
      {D₁ = indexed-category₀ D₁'}
      {C₂ = indexed-category₁ C₂'}
      {D₂ = indexed-category₁ D₂'}
      (indexed-split-functor₀ F₁)
      (indexed-split-functor₁ F₂))
indexed-split-functor-sigma-sum
  {n = suc _} F₁ F₂
  = cons
    (λ x → indexed-split-functor-sigma-sum
      (IndexedSplitFunctor.tail F₁ x)
      (IndexedSplitFunctor.tail F₂ x))
    (λ f → indexed-split-functor-square-sigma-sum
      (IndexedSplitFunctor.indexed-split-functor-square F₁ f)
      (IndexedSplitFunctor.indexed-split-functor-square F₂ f))

-- ### IndexedSplitFunctorSquare

indexed-split-functor-square-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {D₁₁' = D₁₁'} {C₂₁' = C₂₁'} {D₂₁' = D₂₁'}
  {C₁₂' = C₁₂'} {D₁₂' = D₁₂'} {C₂₂' = C₂₂'} {D₂₂' = D₂₂'}
  {F₁' = F₁'} {F₂' = F₂'} {G₂' = G₂'}
  {H₁₁ = H₁₁} {H₂₁ = H₂₁} {H₁₂ = H₁₂} {H₂₂ = H₂₂} s₁ s₂
  = nil
    (split-functor-square-sigma-sum
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {C₁₂ = indexed-category₁ C₁₂'}
      {D₁₂ = indexed-category₁ D₁₂'}
      {C₂₂ = indexed-category₁ C₂₂'}
      {D₂₂ = indexed-category₁ D₂₂'}
      {F₁ = indexed-functor₀ F₁'}
      {F₂ = indexed-functor₁ F₂'}
      {G₂ = indexed-functor₁ G₂'}
      {H₁₁ = indexed-split-functor₀ H₁₁}
      {H₂₁ = indexed-split-functor₀ H₂₁}
      {H₁₂ = indexed-split-functor₁ H₁₂}
      {H₂₂ = indexed-split-functor₁ H₂₂}
      (indexed-split-functor-square₀ s₁)
      (indexed-split-functor-square₁ s₂))
indexed-split-functor-square-sigma-sum
  {n = suc _} s₁ s₂
  = cons
    (λ x₁ → indexed-split-functor-square-sigma-sum
      (IndexedSplitFunctorSquare.tail s₁ x₁)
      (IndexedSplitFunctorSquare.tail s₂ x₁))

