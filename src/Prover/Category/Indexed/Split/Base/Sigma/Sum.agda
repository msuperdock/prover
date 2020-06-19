module Prover.Category.Indexed.Split.Base.Sigma.Sum where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀)
open import Prover.Category.Indexed.Sigma.Sum
  using (indexed-category-sigma-sum)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Category.Indexed.Simple.Sigma.Sum
  using (indexed-simple-category-sigma-sum)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor)
open import Prover.Category.Indexed.Split.Base
  using (IndexedSimpleSplitFunction; IndexedSplitFunction; empty;
    indexed-simple-split-function₀; indexed-split-function₀; sigma)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Category.Split.Base.Sigma.Sum
  using (split-function-sigma-sum)
open import Prover.Prelude

-- ## IndexedSplitFunction

indexed-split-function-sigma-sum
  : {n : ℕ}
  → {A₁₁ A₂₁ A₂₂ : Set}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {C₂₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → (F₁ : IndexedSplitFunctor C₁₁' C₂₁')
  → IndexedSplitFunction A₁₁ C₁₁'
  → IndexedSplitFunction A₂₁ C₂₁'
  → IndexedSplitFunction A₂₂ C₂₂'
  → IndexedSplitFunction
    (A₁₁ ⊔ A₂₁ × A₂₂)
    (indexed-category-sigma-sum C₂₂' F₁)
indexed-split-function-sigma-sum {n = zero} {C₂₂' = C₂₂'} _ G₁₁ G₂₁ G₂₂
  = empty
    (split-function-sigma-sum
      (λ x₂₁ → Category.Object (indexed-category₀
        (IndexedCategory.tail C₂₂' x₂₁)))
      (indexed-split-function₀ G₁₁)
      (indexed-split-function₀ G₂₁)
      (λ x₂₁ → indexed-split-function₀
        (IndexedSplitFunction.tail G₂₂ x₂₁)))
indexed-split-function-sigma-sum {n = suc _} F₁ G₁₁ G₂₁ G₂₂
  = sigma
    (λ x → indexed-split-function-sigma-sum
      (IndexedSplitFunctor.tail F₁ x)
      (IndexedSplitFunction.tail G₁₁ x)
      (IndexedSplitFunction.tail G₂₁ x)
      (IndexedSplitFunction.tail G₂₂ x))

-- ## IndexedSimpleSplitFunction

indexed-simple-split-function-sigma-sum
  : {n : ℕ}
  → {A₁₁ A₂₁ A₂₂ : Set}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {C₂₂' : IndexedSimpleCategory (chain-category-snoc C₂₁')}
  → (F₁ : IndexedSplitFunctor C₁₁' C₂₁')
  → IndexedSplitFunction A₁₁ C₁₁'
  → IndexedSplitFunction A₂₁ C₂₁'
  → IndexedSimpleSplitFunction A₂₂ C₂₂'
  → IndexedSimpleSplitFunction
    (A₁₁ ⊔ A₂₁ × A₂₂)
    (indexed-simple-category-sigma-sum C₂₂' F₁)
indexed-simple-split-function-sigma-sum {n = zero} {C₂₂' = C₂₂'} _ G₁₁ G₂₁ G₂₂
  = empty
    (split-function-sigma-sum
      (λ x₂₁ → indexed-simple-category₀
        (IndexedSimpleCategory.tail C₂₂' x₂₁))
      (indexed-split-function₀ G₁₁)
      (indexed-split-function₀ G₂₁)
      (λ x₂₁ → indexed-simple-split-function₀
        (IndexedSimpleSplitFunction.tail G₂₂ x₂₁)))
indexed-simple-split-function-sigma-sum {n = suc _} F₁ G₁₁ G₂₁ G₂₂
  = sigma
    (λ x → indexed-simple-split-function-sigma-sum
      (IndexedSplitFunctor.tail F₁ x)
      (IndexedSplitFunction.tail G₁₁ x)
      (IndexedSplitFunction.tail G₂₁ x)
      (IndexedSimpleSplitFunction.tail G₂₂ x))

