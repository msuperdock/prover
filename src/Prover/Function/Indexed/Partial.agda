module Prover.Function.Indexed.Partial where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Function.Indexed
  using (IndexedSet; indexed-set₀)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Partial.Compose
  using (partial-function-compose)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definitions

  -- #### IndexedPartialFunction

  data IndexedPartialFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → IndexedSimpleCategory C
    → IndexedSet C
    → Set
    where
  
    empty
      : {C : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSet C}
      → PartialFunction
        (indexed-simple-category₀ C')
        (indexed-set₀ D')
      → IndexedPartialFunction C' D'
  
    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSet C}
      → ((x : Category.Object (ChainCategory.head C))
        → IndexedPartialFunction
          (IndexedSimpleCategory.tail C' x)
          (IndexedSet.tail D' x))
      → IndexedPartialFunction C' D'
  
  -- #### IndexedPartialFunction'
  
  data IndexedPartialFunction'
    : {n : ℕ}
    → {C : ChainCategory n}
    → IndexedSet C
    → IndexedSet C
    → Set
    where
  
    empty
      : {C : ChainCategory zero}
      → {C' D' : IndexedSet C}
      → PartialFunction
        (indexed-set₀ C')
        (indexed-set₀ D')
      → IndexedPartialFunction' C' D'
  
    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' D' : IndexedSet C}
      → ((x : Category.Object (ChainCategory.head C))
        → IndexedPartialFunction'
          (IndexedSet.tail C' x)
          (IndexedSet.tail D' x))
      → IndexedPartialFunction' C' D'
  
  -- ### Interface
  
  -- #### IndexedPartialFunction

  indexed-partial-function₀
    : {C : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSet C}
    → IndexedPartialFunction C' D'
    → PartialFunction
      (indexed-simple-category₀ C')
      (indexed-set₀ D')
  indexed-partial-function₀ (empty f)
    = f
  
  indexed-partial-function-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSet C}
    → IndexedPartialFunction C' D'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedPartialFunction
      (IndexedSimpleCategory.tail C' x)
      (IndexedSet.tail D' x)
  indexed-partial-function-tail (sigma F)
    = F

  -- #### IndexedPartialFunction'
  
  indexed-partial-function₀'
    : {C : ChainCategory zero}
    → {C' D' : IndexedSet C}
    → IndexedPartialFunction' C' D'
    → PartialFunction
      (indexed-set₀ C')
      (indexed-set₀ D')
  indexed-partial-function₀' (empty f)
    = f
  
  indexed-partial-function-tail'
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : IndexedSet C}
    → IndexedPartialFunction' C' D'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedPartialFunction'
      (IndexedSet.tail C' x)
      (IndexedSet.tail D' x)
  indexed-partial-function-tail' (sigma F)
    = F

  -- ### Compose

  indexed-partial-function-compose
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' : IndexedSimpleCategory C}
    → {D' E' : IndexedSet C}
    → IndexedPartialFunction' D' E'
    → IndexedPartialFunction C' D'
    → IndexedPartialFunction C' E'
  indexed-partial-function-compose {n = zero} F G
    = empty
      (partial-function-compose
        (indexed-partial-function₀' F)
        (indexed-partial-function₀ G))
  indexed-partial-function-compose {n = suc _} F G
    = sigma
      (λ x → indexed-partial-function-compose
        (indexed-partial-function-tail' F x)
        (indexed-partial-function-tail G x))

-- ## Modules

open Internal public
  using (IndexedPartialFunction'; indexed-partial-function-compose)

-- ### IndexedPartialFunction

IndexedPartialFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → IndexedSet C
  → Set
IndexedPartialFunction
  = Internal.IndexedPartialFunction

open Internal.IndexedPartialFunction public

open Internal public
  using (indexed-partial-function₀)

module IndexedPartialFunction where

  open Internal public using () renaming
    ( indexed-partial-function-tail
      to tail
    )

