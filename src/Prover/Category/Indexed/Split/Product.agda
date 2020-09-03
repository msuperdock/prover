module Prover.Category.Indexed.Split.Product where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor)
open import Prover.Category.Indexed.Product
  using (indexed-category-product; indexed-functor-product)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor; IndexedSplitFunctorSquare; cons;
    indexed-split-functor₀; indexed-split-functor-square₀; nil)
open import Prover.Category.Split.Product
  using (split-functor-product; split-functor-square-product)
open import Prover.Prelude

-- ## Types

-- ### IndexedSplitFunctor

indexed-split-functor-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' D₁' D₂' : IndexedCategory C}
  → IndexedSplitFunctor C₁' D₁'
  → IndexedSplitFunctor C₂' D₂'
  → IndexedSplitFunctor
    (indexed-category-product C₁' C₂')
    (indexed-category-product D₁' D₂')

-- ### IndexedSplitFunctorSquare

indexed-split-functor-square-product
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁₁' C₁₂' D₁₁' D₁₂' : IndexedCategory C₁}
  → {C₂₁' C₂₂' D₂₁' D₂₂' : IndexedCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → {F₁' : IndexedFunctor C₁₁' C₂₁' F}
  → {F₂' : IndexedFunctor C₁₂' C₂₂' F}
  → {G₁' : IndexedFunctor D₁₁' D₂₁' F}
  → {G₂' : IndexedFunctor D₁₂' D₂₂' F}
  → {H₁₁ : IndexedSplitFunctor C₁₁' D₁₁'}
  → {H₁₂ : IndexedSplitFunctor C₁₂' D₁₂'}
  → {H₂₁ : IndexedSplitFunctor C₂₁' D₂₁'}
  → {H₂₂ : IndexedSplitFunctor C₂₂' D₂₂'}
  → IndexedSplitFunctorSquare F₁' G₁' H₁₁ H₂₁
  → IndexedSplitFunctorSquare F₂' G₂' H₁₂ H₂₂
  → IndexedSplitFunctorSquare
    (indexed-functor-product F₁' F₂')
    (indexed-functor-product G₁' G₂')
    (indexed-split-functor-product H₁₁ H₁₂)
    (indexed-split-functor-product H₂₁ H₂₂)

-- ## Definitions

-- ### IndexedSplitFunctor

indexed-split-functor-product
  {n = zero} F₁ F₂
  = nil
    (split-functor-product
      (indexed-split-functor₀ F₁)
      (indexed-split-functor₀ F₂))
indexed-split-functor-product
  {n = suc _} F₁ F₂
  = cons
    (λ x → indexed-split-functor-product
      (IndexedSplitFunctor.tail F₁ x)
      (IndexedSplitFunctor.tail F₂ x))
    (λ f → indexed-split-functor-square-product
      (IndexedSplitFunctor.indexed-split-functor-square F₁ f)
      (IndexedSplitFunctor.indexed-split-functor-square F₂ f))

-- ### IndexedSplitFunctorSquare

indexed-split-functor-square-product
  {n = zero} s₁ s₂
  = nil
    (split-functor-square-product
      (indexed-split-functor-square₀ s₁)
      (indexed-split-functor-square₀ s₂))
indexed-split-functor-square-product
  {n = suc _} s₁ s₂
  = cons
    (λ x₁ → indexed-split-functor-square-product
      (IndexedSplitFunctorSquare.tail s₁ x₁)
      (IndexedSplitFunctorSquare.tail s₂ x₁))

