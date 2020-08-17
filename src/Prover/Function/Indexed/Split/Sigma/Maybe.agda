module Prover.Function.Indexed.Split.Sigma.Maybe where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀)
open import Prover.Category.Indexed.Sigma.Maybe
  using (indexed-category-sigma-may)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Indexed.Split
  using (IndexedSplitFunction; empty; indexed-split-function₀; sigma)
open import Prover.Function.Split.Sigma
  using (split-function-sigma)
open import Prover.Prelude

-- ## IndexedSplitFunction

indexed-split-function-sigma-may
  : {A₁ A₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : IndexedCategory C}
  → {C₂' : IndexedCategory (chain-category-snoc C₁')}
  → IndexedSplitFunction A₁ C₁'
  → IndexedSplitFunction A₂ C₂'
  → IndexedSplitFunction
    (A₁ × A₂)
    (indexed-category-sigma-may C₁' C₂')
indexed-split-function-sigma-may {n = zero} {C₂' = C₂'} F₁ F₂
  = empty
    (split-function-sigma
      (λ x₁ → Category.Object (indexed-category₀
        (IndexedCategory.tail C₂' x₁)))
      (indexed-split-function₀ F₁)
      (λ x₁ → indexed-split-function₀
        (IndexedSplitFunction.tail F₂ x₁)))
indexed-split-function-sigma-may {n = suc _} F₁ F₂
  = sigma
    (λ x → indexed-split-function-sigma-may
      (IndexedSplitFunction.tail F₁ x)
      (IndexedSplitFunction.tail F₂ x))

