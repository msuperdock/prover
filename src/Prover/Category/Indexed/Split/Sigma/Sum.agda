module Prover.Category.Indexed.Split.Sigma.Sum where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedFunctor; indexed-category₀; indexed-dependent-category₀;
    indexed-dependent-functor₀; indexed-functor₀)
open import Prover.Category.Indexed.Sigma.Maybe
  using (indexed-category-sigma-maybe; indexed-dependent-category-sigma-maybe;
    indexed-dependent-functor-sigma-maybe; indexed-functor-sigma-maybe)
open import Prover.Category.Indexed.Sigma.Sum
  using (indexed-category-sigma-sum; indexed-dependent-category-sigma-sum;
    indexed-dependent-functor-sigma-sum; indexed-functor-sigma-sum)
open import Prover.Category.Indexed.Split
  using (IndexedSplitDependentFunctor; IndexedSplitDependentFunctorSquare;
    IndexedSplitFunctor; IndexedSplitFunctorSquare; empty;
    indexed-split-dependent-functor; indexed-split-dependent-functor₀;
    indexed-split-dependent-functor-square;
    indexed-split-dependent-functor-square₀; indexed-split-functor₀;
    indexed-split-functor-square₀; sigma)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-dependent-category-snoc;
    chain-dependent-functor-snoc; chain-functor-snoc)
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

-- ### IndexedSplitDependentFunctor

indexed-split-dependent-functor-sigma-sum
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C₁'' D₁'' : IndexedDependentCategory C'}
  → {C₂'' D₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₁'')}
  → (F₁ : IndexedSplitDependentFunctor C₁'' D₁'')
  → IndexedSplitDependentFunctor C₂'' D₂''
  → IndexedSplitDependentFunctor
    (indexed-dependent-category-sigma-sum C₂'' F₁)
    (indexed-dependent-category-sigma-maybe D₁'' D₂'')

-- ### IndexedSplitDependentFunctorSquare

indexed-split-dependent-functor-square-sigma-sum
  : {n : ℕ}
  → {C₁ C₂ : Category}
  → {C₁' : ChainDependentCategory C₁ n}
  → {C₂' : ChainDependentCategory C₂ n}
  → {C₁₁'' D₁₁'' : IndexedDependentCategory C₁'}
  → {C₂₁'' D₂₁'' : IndexedDependentCategory C₂'}
  → {C₁₂'' D₁₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₁₁'')}
  → {C₂₂'' D₂₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₂₁'')}
  → {F : ChainDependentFunctor C₁' C₂'}
  → {F₁' : IndexedDependentFunctor C₁₁'' C₂₁'' F}
  → {G₁' : IndexedDependentFunctor D₁₁'' D₂₁'' F}
  → {F₂' : IndexedDependentFunctor C₁₂'' C₂₂''
    (chain-dependent-functor-snoc G₁')}
  → {G₂' : IndexedDependentFunctor D₁₂'' D₂₂''
    (chain-dependent-functor-snoc G₁')}
  → {H₁₁ : IndexedSplitDependentFunctor C₁₁'' D₁₁''}
  → {H₂₁ : IndexedSplitDependentFunctor C₂₁'' D₂₁''}
  → {H₁₂ : IndexedSplitDependentFunctor C₁₂'' D₁₂''}
  → {H₂₂ : IndexedSplitDependentFunctor C₂₂'' D₂₂''}
  → (s₁ : IndexedSplitDependentFunctorSquare F₁' G₁' H₁₁ H₂₁)
  → IndexedSplitDependentFunctorSquare F₂' G₂' H₁₂ H₂₂
  → IndexedSplitDependentFunctorSquare
    (indexed-dependent-functor-sigma-sum F₂' s₁)
    (indexed-dependent-functor-sigma-maybe G₁' G₂')
    (indexed-split-dependent-functor-sigma-sum H₁₁ H₁₂)
    (indexed-split-dependent-functor-sigma-sum H₂₁ H₂₂)

-- ## Definitions

-- ### IndexedSplitFunctor

indexed-split-functor-sigma-sum
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'} {C₂' = C₂'} {D₂' = D₂'} F₁ F₂
  = empty
    (split-functor-sigma-sum
      {C₁ = indexed-category₀ C₁'}
      {D₁ = indexed-category₀ D₁'}
      {C₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂')}
      {D₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₂')}
      (indexed-split-functor₀ F₁)
      (indexed-split-dependent-functor₀
        (IndexedSplitFunctor.unpack F₂)))
indexed-split-functor-sigma-sum
  {n = suc _} F₁ F₂
  = sigma
    (indexed-split-dependent-functor-sigma-sum
      (IndexedSplitFunctor.unpack F₁)
      (IndexedSplitFunctor.unpack F₂))

-- ### IndexedSplitFunctorSquare

indexed-split-functor-square-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {D₁₁' = D₁₁'} {C₂₁' = C₂₁'} {D₂₁' = D₂₁'}
  {C₁₂' = C₁₂'} {D₁₂' = D₁₂'} {C₂₂' = C₂₂'} {D₂₂' = D₂₂'}
  {F₁' = F₁'} {F₂' = F₂'} {G₂' = G₂'}
  {H₁₁ = H₁₁} {H₂₁ = H₂₁} {H₁₂ = H₁₂} {H₂₂ = H₂₂} s₁ s₂
  = empty
    (split-functor-square-sigma-sum
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {C₁₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₁₂')}
      {D₁₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₁₂')}
      {C₂₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂₂')}
      {D₂₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₂₂')}
      {F₁ = indexed-functor₀ F₁'}
      {F₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack F₂')}
      {G₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack G₂')}
      {H₁₁ = indexed-split-functor₀ H₁₁}
      {H₂₁ = indexed-split-functor₀ H₂₁}
      {H₁₂ = indexed-split-dependent-functor₀
        (IndexedSplitFunctor.unpack H₁₂)}
      {H₂₂ = indexed-split-dependent-functor₀
        (IndexedSplitFunctor.unpack H₂₂)}
      (indexed-split-functor-square₀ s₁)
      (indexed-split-dependent-functor-square₀
        (IndexedSplitFunctorSquare.unpack s₂)))
indexed-split-functor-square-sigma-sum
  {n = suc _} s₁ s₂
  = sigma
    (indexed-split-dependent-functor-square-sigma-sum
      (IndexedSplitFunctorSquare.unpack s₁)
      (IndexedSplitFunctorSquare.unpack s₂))

-- ### IndexedSplitDependentFunctor

indexed-split-dependent-functor-sigma-sum F₁ F₂
  = indexed-split-dependent-functor
    (λ x → indexed-split-functor-sigma-sum
      (IndexedSplitDependentFunctor.indexed-split-functor F₁ x)
      (IndexedSplitDependentFunctor.indexed-split-functor F₂ x))
    (λ f → indexed-split-functor-square-sigma-sum
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₁ f)
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₂ f))

-- ### IndexedSplitDependentFunctorSquare

indexed-split-dependent-functor-square-sigma-sum s₁ s₂
  = indexed-split-dependent-functor-square
    (λ x₁ → indexed-split-functor-square-sigma-sum
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₁ x₁)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₂ x₁))

