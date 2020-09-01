module Prover.Function.Indexed.Simple.Bool where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definition

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

  -- ### Interface

  indexed-simple-bool-function₀
    : {C : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → IndexedSimpleBoolFunction C'
    → BoolFunction (indexed-simple-category₀ C')
  indexed-simple-bool-function₀ (empty f)
    = f

  indexed-simple-bool-function-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → IndexedSimpleBoolFunction C'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSimpleBoolFunction
      (IndexedSimpleCategory.tail C' x)
  indexed-simple-bool-function-tail (sigma F)
    = F

-- ## Modules

IndexedSimpleBoolFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → Set
IndexedSimpleBoolFunction
  = Internal.IndexedSimpleBoolFunction

open Internal.IndexedSimpleBoolFunction public

open Internal public
  using (indexed-simple-bool-function₀)

module IndexedSimpleBoolFunction where

  open Internal public using () renaming
    ( indexed-simple-bool-function-tail
      to tail
    )

