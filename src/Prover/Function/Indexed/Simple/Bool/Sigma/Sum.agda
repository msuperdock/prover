module Prover.Function.Indexed.Simple.Bool.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Category.Indexed.Simple.Sigma.Sum
  using (indexed-simple-category-sigma-sum)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Bool.Sigma.Sum
  using (bool-function-sigma-sum)
open import Prover.Function.Indexed.Simple.Bool
  using (IndexedSimpleBoolFunction; cons; indexed-simple-bool-function₀; nil)
open import Prover.Prelude

indexed-simple-bool-function-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {C₂₂' : IndexedSimpleCategory (chain-category-snoc C₂₁')} 
  → (F₁ : IndexedSplitFunctor C₁₁' C₂₁')
  → IndexedSimpleBoolFunction C₂₂'
  → IndexedSimpleBoolFunction (indexed-simple-category-sigma-sum C₂₂' F₁)
indexed-simple-bool-function-sigma-sum
  {n = zero} {C₂₂' = C₂₂'} _ G₂₂
  = nil
    (bool-function-sigma-sum
      (λ x₂₁ → indexed-simple-category₀
        (IndexedSimpleCategory.tail C₂₂' x₂₁))
      (λ x₂₁ → indexed-simple-bool-function₀
        (IndexedSimpleBoolFunction.tail G₂₂ x₂₁)))
indexed-simple-bool-function-sigma-sum
  {n = suc _} F₁ G₂₂
  = cons
    (λ x → indexed-simple-bool-function-sigma-sum
      (IndexedSplitFunctor.tail F₁ x)
      (IndexedSimpleBoolFunction.tail G₂₂ x))

