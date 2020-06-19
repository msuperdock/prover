module Prover.Category.Indexed.Split.Base where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor; indexed-split-functor₀)
open import Prover.Category.Split.Base
  using (SplitFunction; split-functor-base)
open import Prover.Category.Split.Base.Compose
  using (split-function-compose)
open import Prover.Prelude

-- ## Internal

module Internal where
  
  -- ### IndexedSplitFunction
  
  -- #### Definition

  data IndexedSplitFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → Set
    → IndexedCategory C
    → Set
    where
  
    empty
      : {A : Set}
      → {C : ChainCategory zero}
      → {C' : IndexedCategory C}
      → SplitFunction A (Category.Object (indexed-category₀ C'))
      → IndexedSplitFunction A C'
  
    sigma
      : {n : ℕ}
      → {A : Set}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedCategory C}
      → ((x : Category.Object (ChainCategory.head C))
        → IndexedSplitFunction A (IndexedCategory.tail C' x))
      → IndexedSplitFunction A C'
  
  -- #### Interface

  indexed-split-function₀
    : {A : Set}
    → {C : ChainCategory zero}
    → {C' : IndexedCategory C}
    → IndexedSplitFunction A C'
    → SplitFunction A (Category.Object (indexed-category₀ C'))
  indexed-split-function₀ (empty F)
    = F

  indexed-split-function-tail
    : {n : ℕ}
    → {A : Set}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → IndexedSplitFunction A C'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSplitFunction A (IndexedCategory.tail C' x)
  indexed-split-function-tail (sigma F)
    = F

  -- #### Compose

  indexed-split-function-compose
    : {A B : Set}
    → {n : ℕ}
    → {C : ChainCategory n}
    → {C' : IndexedCategory C}
    → IndexedSplitFunction B C'
    → SplitFunction A B
    → IndexedSplitFunction A C'
  indexed-split-function-compose {n = zero} F G
    = empty
      (split-function-compose
        (indexed-split-function₀ F) G)
  indexed-split-function-compose {n = suc _} F G
    = sigma
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
  indexed-split-function-compose' {n = zero} F G
    = empty
      (split-function-compose
        (split-functor-base
          (indexed-split-functor₀ F))
        (indexed-split-function₀ G))
  indexed-split-function-compose' {n = suc _} F G
    = sigma
      (λ x → indexed-split-function-compose'
        (IndexedSplitFunctor.tail F x)
        (indexed-split-function-tail G x))

  -- ### IndexedSimpleSplitFunction
  
  -- #### Definition
  
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
  
  -- #### Interface
  
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

  -- #### Compose
  
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

-- ## Modules

-- ### IndexedSplitFunction

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

  open Internal.IndexedSplitFunction public

  open Internal public using () renaming
    ( indexed-split-function-tail
      to tail
    )

-- ### IndexedSimpleSplitFunction

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

  open Internal.IndexedSimpleSplitFunction public

  open Internal public using () renaming
    ( indexed-simple-split-function-tail
      to tail
    )

