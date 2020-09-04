module Prover.Function.Dependent.Simple.Split where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; dependent-simple-category₀)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Function.Split.Compose
  using (split-function-compose)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definition
  
  data DependentSimpleSplitFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → Set
    → DependentSimpleCategory C
    → Set
    where
  
    nil
      : {A : Set}
      → {C : ChainCategory zero}
      → {C' : DependentSimpleCategory C}
      → SplitFunction A (dependent-simple-category₀ C')
      → DependentSimpleSplitFunction A C'
  
    cons
      : {n : ℕ}
      → {A : Set}
      → {C : ChainCategory (suc n)}
      → {C' : DependentSimpleCategory C}
      → ((x : Category.Object (ChainCategory.head C))
        → DependentSimpleSplitFunction A (DependentSimpleCategory.tail C' x))
      → DependentSimpleSplitFunction A C'
  
  -- ### Interface
  
  dependent-simple-split-function₀
    : {A : Set}
    → {C : ChainCategory zero}
    → {C' : DependentSimpleCategory C}
    → DependentSimpleSplitFunction A C'
    → SplitFunction A (dependent-simple-category₀ C')
  dependent-simple-split-function₀ (nil F)
    = F
  
  dependent-simple-split-function-tail
    : {n : ℕ}
    → {A : Set}
    → {C : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → DependentSimpleSplitFunction A C'
    → (x : Category.Object (ChainCategory.head C))
    → DependentSimpleSplitFunction A (DependentSimpleCategory.tail C' x)
  dependent-simple-split-function-tail (cons F)
    = F

  -- ### Compose
  
  dependent-simple-split-function-compose
    : {A B : Set}
    → {n : ℕ}
    → {C : ChainCategory n}
    → {C' : DependentSimpleCategory C}
    → DependentSimpleSplitFunction B C'
    → SplitFunction A B
    → DependentSimpleSplitFunction A C'
  dependent-simple-split-function-compose
    {n = zero} F G
    = nil
      (split-function-compose
        (dependent-simple-split-function₀ F) G)
  dependent-simple-split-function-compose
    {n = suc _} F G
    = cons
      (λ x → dependent-simple-split-function-compose
        (dependent-simple-split-function-tail F x) G)

-- ## Module

DependentSimpleSplitFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → Set
  → DependentSimpleCategory C
  → Set
DependentSimpleSplitFunction
  = Internal.DependentSimpleSplitFunction

open Internal.DependentSimpleSplitFunction public

open Internal public
  using (dependent-simple-split-function₀;
    dependent-simple-split-function-compose)

module DependentSimpleSplitFunction where

  open Internal public using () renaming
    ( dependent-simple-split-function-tail
      to tail
    )

