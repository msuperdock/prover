module Prover.Function.Dependent.Simple.Partial where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; dependent-simple-category₀)
open import Prover.Function.Dependent
  using (DependentSet; dependent-set₀)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Partial.Compose
  using (partial-function-compose)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definitions

  -- #### DependentSimplePartialFunction

  data DependentSimplePartialFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → DependentSimpleCategory C
    → DependentSet C
    → Set
    where
  
    nil
      : {C : ChainCategory zero}
      → {C' : DependentSimpleCategory C}
      → {D' : DependentSet C}
      → PartialFunction
        (dependent-simple-category₀ C')
        (dependent-set₀ D')
      → DependentSimplePartialFunction C' D'
  
    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : DependentSimpleCategory C}
      → {D' : DependentSet C}
      → ((x : Category.Object (ChainCategory.head C))
        → DependentSimplePartialFunction
          (DependentSimpleCategory.tail C' x)
          (DependentSet.tail D' x))
      → DependentSimplePartialFunction C' D'
  
  -- #### DependentSimplePartialFunction'
  
  data DependentSimplePartialFunction'
    : {n : ℕ}
    → {C : ChainCategory n}
    → DependentSet C
    → DependentSet C
    → Set
    where
  
    nil
      : {C : ChainCategory zero}
      → {C' D' : DependentSet C}
      → PartialFunction
        (dependent-set₀ C')
        (dependent-set₀ D')
      → DependentSimplePartialFunction' C' D'
  
    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' D' : DependentSet C}
      → ((x : Category.Object (ChainCategory.head C))
        → DependentSimplePartialFunction'
          (DependentSet.tail C' x)
          (DependentSet.tail D' x))
      → DependentSimplePartialFunction' C' D'
  
  -- ### Interface
  
  -- #### DependentSimplePartialFunction

  dependent-simple-partial-function₀
    : {C : ChainCategory zero}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSet C}
    → DependentSimplePartialFunction C' D'
    → PartialFunction
      (dependent-simple-category₀ C')
      (dependent-set₀ D')
  dependent-simple-partial-function₀ (nil f)
    = f
  
  dependent-simple-partial-function-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSet C}
    → DependentSimplePartialFunction C' D'
    → (x : Category.Object (ChainCategory.head C))
    → DependentSimplePartialFunction
      (DependentSimpleCategory.tail C' x)
      (DependentSet.tail D' x)
  dependent-simple-partial-function-tail (cons F)
    = F

  -- #### DependentSimplePartialFunction'
  
  dependent-simple-partial-function₀'
    : {C : ChainCategory zero}
    → {C' D' : DependentSet C}
    → DependentSimplePartialFunction' C' D'
    → PartialFunction
      (dependent-set₀ C')
      (dependent-set₀ D')
  dependent-simple-partial-function₀' (nil f)
    = f
  
  dependent-simple-partial-function-tail'
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : DependentSet C}
    → DependentSimplePartialFunction' C' D'
    → (x : Category.Object (ChainCategory.head C))
    → DependentSimplePartialFunction'
      (DependentSet.tail C' x)
      (DependentSet.tail D' x)
  dependent-simple-partial-function-tail' (cons F)
    = F

  -- ### Compose

  dependent-simple-partial-function-compose
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' : DependentSimpleCategory C}
    → {D' E' : DependentSet C}
    → DependentSimplePartialFunction' D' E'
    → DependentSimplePartialFunction C' D'
    → DependentSimplePartialFunction C' E'
  dependent-simple-partial-function-compose
    {n = zero} F G
    = nil
      (partial-function-compose
        (dependent-simple-partial-function₀' F)
        (dependent-simple-partial-function₀ G))
  dependent-simple-partial-function-compose
    {n = suc _} F G
    = cons
      (λ x → dependent-simple-partial-function-compose
        (dependent-simple-partial-function-tail' F x)
        (dependent-simple-partial-function-tail G x))

-- ## Modules

open Internal public
  using (DependentSimplePartialFunction';
    dependent-simple-partial-function-compose)

-- ### DependentSimplePartialFunction

DependentSimplePartialFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentSet C
  → Set
DependentSimplePartialFunction
  = Internal.DependentSimplePartialFunction

open Internal.DependentSimplePartialFunction public

open Internal public
  using (dependent-simple-partial-function₀)

module DependentSimplePartialFunction where

  open Internal public using () renaming
    ( dependent-simple-partial-function-tail
      to tail
    )

