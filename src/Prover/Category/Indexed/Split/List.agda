module Prover.Category.Indexed.Split.List where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedFunctor; indexed-category₀; indexed-functor₀)
open import Prover.Category.Indexed.List
  using (indexed-category-list; indexed-dependent-category-list;
    indexed-dependent-functor-list; indexed-functor-list)
open import Prover.Category.Indexed.Split
  using (IndexedSplitDependentFunctor; IndexedSplitDependentFunctorSquare;
    IndexedSplitFunctor; IndexedSplitFunctorSquare; empty;
    indexed-split-dependent-functor; indexed-split-dependent-functor-square;
    indexed-split-functor₀; indexed-split-functor-square₀; sigma)
open import Prover.Category.Split.List
  using (split-functor-list; split-functor-square-list)
open import Prover.Prelude

-- ## Types

-- ### IndexedSplitFunctor

indexed-split-functor-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : IndexedCategory C}
  → IndexedSplitFunctor C' D'
  → IndexedSplitFunctor
    (indexed-category-list C')
    (indexed-category-list D')

-- ### IndexedSplitFunctorSquare

indexed-split-functor-square-list
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' D₁' : IndexedCategory C₁}
  → {C₂' D₂' : IndexedCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → {F' : IndexedFunctor C₁' C₂' F}
  → {G' : IndexedFunctor D₁' D₂' F}
  → {H₁ : IndexedSplitFunctor C₁' D₁'}
  → {H₂ : IndexedSplitFunctor C₂' D₂'}
  → IndexedSplitFunctorSquare F' G' H₁ H₂
  → IndexedSplitFunctorSquare
    (indexed-functor-list F')
    (indexed-functor-list G')
    (indexed-split-functor-list H₁)
    (indexed-split-functor-list H₂)

-- ### IndexedSplitDependentFunctor

indexed-split-dependent-functor-list
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C'' D'' : IndexedDependentCategory C'}
  → IndexedSplitDependentFunctor C'' D''
  → IndexedSplitDependentFunctor
    (indexed-dependent-category-list C'')
    (indexed-dependent-category-list D'')

-- ### IndexedSplitDependentFunctorSquare

indexed-split-dependent-functor-square-list
  : {n : ℕ}
  → {C₁ C₂ : Category}
  → {C₁' : ChainDependentCategory C₁ n}
  → {C₂' : ChainDependentCategory C₂ n}
  → {C₁'' D₁'' : IndexedDependentCategory C₁'}
  → {C₂'' D₂'' : IndexedDependentCategory C₂'}
  → {F : ChainDependentFunctor C₁' C₂'}
  → {F' : IndexedDependentFunctor C₁'' C₂'' F}
  → {G' : IndexedDependentFunctor D₁'' D₂'' F}
  → {H₁ : IndexedSplitDependentFunctor C₁'' D₁''}
  → {H₂ : IndexedSplitDependentFunctor C₂'' D₂''}
  → IndexedSplitDependentFunctorSquare F' G' H₁ H₂
  → IndexedSplitDependentFunctorSquare
    (indexed-dependent-functor-list F')
    (indexed-dependent-functor-list G')
    (indexed-split-dependent-functor-list H₁)
    (indexed-split-dependent-functor-list H₂)

-- ## Definitions

-- ### IndexedSplitFunctor

indexed-split-functor-list
  {n = zero}
  {C' = C'} {D' = D'} F
  = empty
    (split-functor-list
      {C = indexed-category₀ C'}
      {D = indexed-category₀ D'}
      (indexed-split-functor₀ F))
indexed-split-functor-list
  {n = suc _} F
  = sigma
    (indexed-split-dependent-functor-list
      (IndexedSplitFunctor.unpack F))

-- ### IndexedSplitFunctorSquare

indexed-split-functor-square-list
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'}
  {C₂' = C₂'} {D₂' = D₂'} 
  {F' = F'} {G' = G'}
  {H₁ = H₁} {H₂ = H₂} s
  = empty
    (split-functor-square-list
      {C₁ = indexed-category₀ C₁'}
      {C₂ = indexed-category₀ C₂'}
      {D₁ = indexed-category₀ D₁'}
      {D₂ = indexed-category₀ D₂'}
      {F = indexed-functor₀ F'}
      {G = indexed-functor₀ G'}
      {H₁ = indexed-split-functor₀ H₁}
      {H₂ = indexed-split-functor₀ H₂}
      (indexed-split-functor-square₀ s))
indexed-split-functor-square-list
  {n = suc _} s
  = sigma
    (indexed-split-dependent-functor-square-list
      (IndexedSplitFunctorSquare.unpack s))

-- ### IndexedSplitDependentFunctor

indexed-split-dependent-functor-list F
  = indexed-split-dependent-functor
    (λ x → indexed-split-functor-list
      (IndexedSplitDependentFunctor.indexed-split-functor F x))
    (λ f → indexed-split-functor-square-list
      (IndexedSplitDependentFunctor.indexed-split-functor-square F f))

-- ### IndexedSplitDependentFunctorSquare

indexed-split-dependent-functor-square-list s
  = indexed-split-dependent-functor-square
    (λ x₁ → indexed-split-functor-square-list
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s x₁))

