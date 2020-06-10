module Prover.Category.Indexed.Split.Product where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedFunctor; indexed-category₀; indexed-functor₀)
open import Prover.Category.Indexed.Product
  using (indexed-category-product; indexed-dependent-category-product;
    indexed-dependent-functor-product; indexed-functor-product)
open import Prover.Category.Indexed.Split
  using (IndexedSplitDependentFunctor; IndexedSplitDependentFunctorSquare;
    IndexedSplitFunctor; IndexedSplitFunctorSquare; empty;
    indexed-split-dependent-functor; indexed-split-dependent-functor-square;
    indexed-split-functor₀; indexed-split-functor-square₀; sigma)
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

-- ### IndexedSplitDependentFunctor

indexed-split-dependent-functor-product
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C₁'' C₂'' D₁'' D₂'' : IndexedDependentCategory C'}
  → IndexedSplitDependentFunctor C₁'' D₁''
  → IndexedSplitDependentFunctor C₂'' D₂''
  → IndexedSplitDependentFunctor
    (indexed-dependent-category-product C₁'' C₂'')
    (indexed-dependent-category-product D₁'' D₂'')

-- ### IndexedSplitDependentFunctorSquare

indexed-split-dependent-functor-square-product
  : {n : ℕ}
  → {C₁ C₂ : Category}
  → {C₁' : ChainDependentCategory C₁ n}
  → {C₂' : ChainDependentCategory C₂ n}
  → {C₁₁'' C₁₂'' D₁₁'' D₁₂'' : IndexedDependentCategory C₁'}
  → {C₂₁'' C₂₂'' D₂₁'' D₂₂'' : IndexedDependentCategory C₂'}
  → {F : ChainDependentFunctor C₁' C₂'}
  → {F₁' : IndexedDependentFunctor C₁₁'' C₂₁'' F}
  → {F₂' : IndexedDependentFunctor C₁₂'' C₂₂'' F}
  → {G₁' : IndexedDependentFunctor D₁₁'' D₂₁'' F}
  → {G₂' : IndexedDependentFunctor D₁₂'' D₂₂'' F}
  → {H₁₁ : IndexedSplitDependentFunctor C₁₁'' D₁₁''}
  → {H₁₂ : IndexedSplitDependentFunctor C₁₂'' D₁₂''}
  → {H₂₁ : IndexedSplitDependentFunctor C₂₁'' D₂₁''}
  → {H₂₂ : IndexedSplitDependentFunctor C₂₂'' D₂₂''}
  → IndexedSplitDependentFunctorSquare F₁' G₁' H₁₁ H₂₁
  → IndexedSplitDependentFunctorSquare F₂' G₂' H₁₂ H₂₂
  → IndexedSplitDependentFunctorSquare
    (indexed-dependent-functor-product F₁' F₂')
    (indexed-dependent-functor-product G₁' G₂')
    (indexed-split-dependent-functor-product H₁₁ H₁₂)
    (indexed-split-dependent-functor-product H₂₁ H₂₂)

-- ## Definitions

-- ### IndexedSplitFunctor

indexed-split-functor-product
  {n = zero}
  {C₁' = C₁'} {C₂' = C₂'} {D₁' = D₁'} {D₂' = D₂'} F₁ F₂
  = empty
    (split-functor-product
      {C₁ = indexed-category₀ C₁'}
      {C₂ = indexed-category₀ C₂'}
      {D₁ = indexed-category₀ D₁'}
      {D₂ = indexed-category₀ D₂'}
      (indexed-split-functor₀ F₁)
      (indexed-split-functor₀ F₂))
indexed-split-functor-product
  {n = suc _} F₁ F₂
  = sigma
    (indexed-split-dependent-functor-product
      (IndexedSplitFunctor.unpack F₁)
      (IndexedSplitFunctor.unpack F₂))

-- ### IndexedSplitFunctorSquare

indexed-split-functor-square-product
  {n = zero}
  {C₁₁' = C₁₁'} {C₁₂' = C₁₂'} {D₁₁' = D₁₁'} {D₁₂' = D₁₂'}
  {C₂₁' = C₂₁'} {C₂₂' = C₂₂'} {D₂₁' = D₂₁'} {D₂₂' = D₂₂'}
  {F₁' = F₁'} {F₂' = F₂'} {G₁' = G₁'} {G₂' = G₂'}
  {H₁₁ = H₁₁} {H₁₂ = H₁₂} {H₂₁ = H₂₁} {H₂₂ = H₂₂} s₁ s₂
  = empty
    (split-functor-square-product
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₁₂ = indexed-category₀ C₁₂'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {C₂₂ = indexed-category₀ C₂₂'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₁₂ = indexed-category₀ D₁₂'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {D₂₂ = indexed-category₀ D₂₂'}
      {F₁ = indexed-functor₀ F₁'}
      {F₂ = indexed-functor₀ F₂'}
      {G₁ = indexed-functor₀ G₁'}
      {G₂ = indexed-functor₀ G₂'}
      {H₁₁ = indexed-split-functor₀ H₁₁}
      {H₁₂ = indexed-split-functor₀ H₁₂}
      {H₂₁ = indexed-split-functor₀ H₂₁}
      {H₂₂ = indexed-split-functor₀ H₂₂}
      (indexed-split-functor-square₀ s₁)
      (indexed-split-functor-square₀ s₂))
indexed-split-functor-square-product
  {n = suc _} s₁ s₂
  = sigma
    (indexed-split-dependent-functor-square-product
      (IndexedSplitFunctorSquare.unpack s₁)
      (IndexedSplitFunctorSquare.unpack s₂))

-- ### IndexedSplitDependentFunctor

indexed-split-dependent-functor-product F₁ F₂
  = indexed-split-dependent-functor
    (λ x → indexed-split-functor-product
      (IndexedSplitDependentFunctor.indexed-split-functor F₁ x)
      (IndexedSplitDependentFunctor.indexed-split-functor F₂ x))
    (λ f → indexed-split-functor-square-product
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₁ f)
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₂ f))

-- ### IndexedSplitDependentFunctorSquare

indexed-split-dependent-functor-square-product s₁ s₂
  = indexed-split-dependent-functor-square
    (λ x₁ → indexed-split-functor-square-product
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₁ x₁)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₂ x₁))

