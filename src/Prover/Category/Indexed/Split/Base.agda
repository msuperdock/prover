module Prover.Category.Indexed.Split.Base where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Category.Split.Base
  using (SplitFunction)
open import Prover.Prelude

-- ## IndexedSplitFunction

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

-- ## IndexedSimpleSplitFunction

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

