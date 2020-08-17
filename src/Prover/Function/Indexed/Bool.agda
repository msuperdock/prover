module Prover.Function.Indexed.Bool where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Prelude

data IndexedSimpleBoolFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → Set
  where

  empty
    : {C : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → BoolFunction (indexed-simple-category₀ C')
    → IndexedSimpleBoolFunction C'

  sigma
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → ((x : Category.Object (ChainCategory.head C))
      → IndexedSimpleBoolFunction (IndexedSimpleCategory.tail C' x))
    → IndexedSimpleBoolFunction C'

