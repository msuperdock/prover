module Prover.Function.Indexed.Split where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor; indexed-split-functor₀)
open import Prover.Function.Split
  using (SplitFunction; split-functor-base)
open import Prover.Function.Split.Compose
  using (split-function-compose)
open import Prover.Prelude

-- ## Internal

module Internal where
  
  -- ### Definition

  data IndexedSplitFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → Set
    → IndexedCategory C
    → Set
    where
  
    nil
      : {A : Set}
      → {C : ChainCategory zero}
      → {C' : IndexedCategory C}
      → SplitFunction A (Category.Object (indexed-category₀ C'))
      → IndexedSplitFunction A C'
  
    cons
      : {n : ℕ}
      → {A : Set}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedCategory C}
      → ((x : Category.Object (ChainCategory.head C))
        → IndexedSplitFunction A (IndexedCategory.tail C' x))
      → IndexedSplitFunction A C'
  
  -- ### Interface

  indexed-split-function₀
    : {A : Set}
    → {C : ChainCategory zero}
    → {C' : IndexedCategory C}
    → IndexedSplitFunction A C'
    → SplitFunction A (Category.Object (indexed-category₀ C'))
  indexed-split-function₀ (nil F)
    = F

  indexed-split-function-tail
    : {n : ℕ}
    → {A : Set}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → IndexedSplitFunction A C'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSplitFunction A (IndexedCategory.tail C' x)
  indexed-split-function-tail (cons F)
    = F

  -- ### Compose

  indexed-split-function-compose
    : {A B : Set}
    → {n : ℕ}
    → {C : ChainCategory n}
    → {C' : IndexedCategory C}
    → IndexedSplitFunction B C'
    → SplitFunction A B
    → IndexedSplitFunction A C'
  indexed-split-function-compose
    {n = zero} F G
    = nil
      (split-function-compose
        (indexed-split-function₀ F) G)
  indexed-split-function-compose
    {n = suc _} F G
    = cons
      (λ x → indexed-split-function-compose
        (indexed-split-function-tail F x) G)

  indexed-split-function-compose'
    : {A : Set}
    → {n : ℕ}
    → {C : ChainCategory n}
    → {C' D' : IndexedCategory C}
    → IndexedSplitFunctor C' D'
    → IndexedSplitFunction A C'
    → IndexedSplitFunction A D'
  indexed-split-function-compose'
    {n = zero} F G
    = nil
      (split-function-compose
        (split-functor-base
          (indexed-split-functor₀ F))
        (indexed-split-function₀ G))
  indexed-split-function-compose'
    {n = suc _} F G
    = cons
      (λ x → indexed-split-function-compose'
        (IndexedSplitFunctor.tail F x)
        (indexed-split-function-tail G x))

-- ## Modules

IndexedSplitFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → Set
  → IndexedCategory C
  → Set
IndexedSplitFunction
  = Internal.IndexedSplitFunction

open Internal.IndexedSplitFunction public

open Internal public
  using (indexed-split-function₀; indexed-split-function-compose;
    indexed-split-function-compose')

module IndexedSplitFunction where

  open Internal public using () renaming
    ( indexed-split-function-tail
      to tail
    )

