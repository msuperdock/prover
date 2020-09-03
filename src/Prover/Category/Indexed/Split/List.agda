module Prover.Category.Indexed.Split.List where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor)
open import Prover.Category.Indexed.List
  using (indexed-category-list; indexed-functor-list)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor; IndexedSplitFunctorSquare; cons;
    indexed-split-functor₀; indexed-split-functor-square₀; nil)
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

-- ## Definitions

-- ### IndexedSplitFunctor

indexed-split-functor-list
  {n = zero} F
  = nil
    (split-functor-list
      (indexed-split-functor₀ F))
indexed-split-functor-list
  {n = suc _} F
  = cons
    (λ x → indexed-split-functor-list
      (IndexedSplitFunctor.tail F x))
    (λ f → indexed-split-functor-square-list
      (IndexedSplitFunctor.indexed-split-functor-square F f))

-- ### IndexedSplitFunctorSquare

indexed-split-functor-square-list
  {n = zero} s
  = nil
    (split-functor-square-list
      (indexed-split-functor-square₀ s))
indexed-split-functor-square-list
  {n = suc _} s
  = cons
    (λ x₁ → indexed-split-functor-square-list
      (IndexedSplitFunctorSquare.tail s x₁))

