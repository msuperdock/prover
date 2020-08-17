module Prover.Function.Indexed.Partial.Sigma.Sum where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Category.Indexed.Simple.Sigma.Sum
  using (indexed-simple-category-sigma-sum)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Indexed
  using (IndexedSet; indexed-set₀)
open import Prover.Function.Indexed.Partial
  using (IndexedPartialFunction; empty; indexed-partial-function₀; sigma)
open import Prover.Function.Indexed.Sigma
  using (indexed-set-sigma)
open import Prover.Function.Partial.Sigma.Sum
  using (partial-function-sigma-sum)
open import Prover.Prelude

-- ## IndexedPartialFunction

indexed-partial-function-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' D₁' : IndexedCategory C}
  → {C₂' : IndexedSimpleCategory (chain-category-snoc D₁')}
  → {D₂' : IndexedSet (chain-category-snoc D₁')}
  → (F₁ : IndexedSplitFunctor C₁' D₁')
  → IndexedPartialFunction C₂' D₂'
  → IndexedPartialFunction
    (indexed-simple-category-sigma-sum C₂' F₁)
    (indexed-set-sigma D₁' D₂')
indexed-partial-function-sigma-sum
  {n = zero} {C₁' = C₁'} {D₁' = D₁'} {C₂' = C₂'} {D₂' = D₂'} _ F₂
  = empty
    (partial-function-sigma-sum
      (Category.Object
        (indexed-category₀ C₁'))
      (Category.Object
        (indexed-category₀ D₁'))
      (λ y₁ → indexed-simple-category₀
        (IndexedSimpleCategory.tail C₂' y₁))
      (λ y₁ → indexed-set₀
        (IndexedSet.tail D₂' y₁))
      (λ y₁ → indexed-partial-function₀
        (IndexedPartialFunction.tail F₂ y₁)))
indexed-partial-function-sigma-sum
  {n = suc _} F₁ F₂
  = sigma
    (λ x → indexed-partial-function-sigma-sum
      (IndexedSplitFunctor.tail F₁ x)
      (IndexedPartialFunction.tail F₂ x))

