module Prover.Function.Indexed.Simple.Split where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Function.Split.Compose
  using (split-function-compose)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definition
  
  data IndexedSimpleSplitFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → Set
    → IndexedSimpleCategory C
    → Set
    where
  
    empty
      : {A : Set}
      → {C : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → SplitFunction A (indexed-simple-category₀ C')
      → IndexedSimpleSplitFunction A C'
  
    sigma
      : {n : ℕ}
      → {A : Set}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → ((x : Category.Object (ChainCategory.head C))
        → IndexedSimpleSplitFunction A (IndexedSimpleCategory.tail C' x))
      → IndexedSimpleSplitFunction A C'
  
  -- ### Interface
  
  indexed-simple-split-function₀
    : {A : Set}
    → {C : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → IndexedSimpleSplitFunction A C'
    → SplitFunction A (indexed-simple-category₀ C')
  indexed-simple-split-function₀ (empty F)
    = F
  
  indexed-simple-split-function-tail
    : {n : ℕ}
    → {A : Set}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → IndexedSimpleSplitFunction A C'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSimpleSplitFunction A (IndexedSimpleCategory.tail C' x)
  indexed-simple-split-function-tail (sigma F)
    = F

  -- ### Compose
  
  indexed-simple-split-function-compose
    : {A B : Set}
    → {n : ℕ}
    → {C : ChainCategory n}
    → {C' : IndexedSimpleCategory C}
    → IndexedSimpleSplitFunction B C'
    → SplitFunction A B
    → IndexedSimpleSplitFunction A C'
  indexed-simple-split-function-compose {n = zero} F G
    = empty
      (split-function-compose
        (indexed-simple-split-function₀ F) G)
  indexed-simple-split-function-compose {n = suc _} F G
    = sigma
      (λ x → indexed-simple-split-function-compose
        (indexed-simple-split-function-tail F x) G)

-- ## Module

IndexedSimpleSplitFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → Set
  → IndexedSimpleCategory C
  → Set
IndexedSimpleSplitFunction
  = Internal.IndexedSimpleSplitFunction

open Internal.IndexedSimpleSplitFunction public

open Internal public
  using (indexed-simple-split-function₀; indexed-simple-split-function-compose)

module IndexedSimpleSplitFunction where

  open Internal public using () renaming
    ( indexed-simple-split-function-tail
      to tail
    )

