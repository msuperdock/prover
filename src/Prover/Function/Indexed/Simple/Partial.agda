module Prover.Function.Indexed.Simple.Partial where

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

  -- #### IndexedSimplePartialFunction

  data IndexedSimplePartialFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → IndexedSimpleCategory C
    → IndexedSet C
    → Set
    where
  
    nil
      : {C : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSet C}
      → PartialFunction
        (indexed-simple-category₀ C')
        (indexed-set₀ D')
      → IndexedSimplePartialFunction C' D'
  
    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSet C}
      → ((x : Category.Object (ChainCategory.head C))
        → IndexedSimplePartialFunction
          (IndexedSimpleCategory.tail C' x)
          (IndexedSet.tail D' x))
      → IndexedSimplePartialFunction C' D'
  
  -- #### IndexedSimplePartialFunction'
  
  data IndexedSimplePartialFunction'
    : {n : ℕ}
    → {C : ChainCategory n}
    → IndexedSet C
    → IndexedSet C
    → Set
    where
  
    nil
      : {C : ChainCategory zero}
      → {C' D' : IndexedSet C}
      → PartialFunction
        (indexed-set₀ C')
        (indexed-set₀ D')
      → IndexedSimplePartialFunction' C' D'
  
    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' D' : IndexedSet C}
      → ((x : Category.Object (ChainCategory.head C))
        → IndexedSimplePartialFunction'
          (IndexedSet.tail C' x)
          (IndexedSet.tail D' x))
      → IndexedSimplePartialFunction' C' D'
  
  -- ### Interface
  
  -- #### IndexedSimplePartialFunction

  indexed-simple-partial-function₀
    : {C : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSet C}
    → IndexedSimplePartialFunction C' D'
    → PartialFunction
      (indexed-simple-category₀ C')
      (indexed-set₀ D')
  indexed-simple-partial-function₀ (nil f)
    = f
  
  indexed-simple-partial-function-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSet C}
    → IndexedSimplePartialFunction C' D'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSimplePartialFunction
      (IndexedSimpleCategory.tail C' x)
      (IndexedSet.tail D' x)
  indexed-simple-partial-function-tail (cons F)
    = F

  -- #### IndexedSimplePartialFunction'
  
  indexed-simple-partial-function₀'
    : {C : ChainCategory zero}
    → {C' D' : IndexedSet C}
    → IndexedSimplePartialFunction' C' D'
    → PartialFunction
      (indexed-set₀ C')
      (indexed-set₀ D')
  indexed-simple-partial-function₀' (nil f)
    = f
  
  indexed-simple-partial-function-tail'
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : IndexedSet C}
    → IndexedSimplePartialFunction' C' D'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSimplePartialFunction'
      (IndexedSet.tail C' x)
      (IndexedSet.tail D' x)
  indexed-simple-partial-function-tail' (cons F)
    = F

  -- ### Compose

  indexed-simple-partial-function-compose
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' : IndexedSimpleCategory C}
    → {D' E' : IndexedSet C}
    → IndexedSimplePartialFunction' D' E'
    → IndexedSimplePartialFunction C' D'
    → IndexedSimplePartialFunction C' E'
  indexed-simple-partial-function-compose
    {n = zero} F G
    = nil
      (partial-function-compose
        (indexed-simple-partial-function₀' F)
        (indexed-simple-partial-function₀ G))
  indexed-simple-partial-function-compose
    {n = suc _} F G
    = cons
      (λ x → indexed-simple-partial-function-compose
        (indexed-simple-partial-function-tail' F x)
        (indexed-simple-partial-function-tail G x))

-- ## Modules

open Internal public
  using (IndexedSimplePartialFunction'; indexed-simple-partial-function-compose)

-- ### IndexedSimplePartialFunction

IndexedSimplePartialFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → IndexedSet C
  → Set
IndexedSimplePartialFunction
  = Internal.IndexedSimplePartialFunction

open Internal.IndexedSimplePartialFunction public

open Internal public
  using (indexed-simple-partial-function₀)

module IndexedSimplePartialFunction where

  open Internal public using () renaming
    ( indexed-simple-partial-function-tail
      to tail
    )

