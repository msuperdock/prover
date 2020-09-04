module Prover.Function.Dependent.Split where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory; dependent-category₀)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; dependent-split-functor₀)
open import Prover.Function.Split
  using (SplitFunction; split-functor-base)
open import Prover.Function.Split.Compose
  using (split-function-compose)
open import Prover.Prelude

-- ## Internal

module Internal where
  
  -- ### Definition

  data DependentSplitFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → Set
    → DependentCategory C
    → Set
    where
  
    nil
      : {A : Set}
      → {C : ChainCategory zero}
      → {C' : DependentCategory C}
      → SplitFunction A (Category.Object (dependent-category₀ C'))
      → DependentSplitFunction A C'
  
    cons
      : {n : ℕ}
      → {A : Set}
      → {C : ChainCategory (suc n)}
      → {C' : DependentCategory C}
      → ((x : Category.Object (ChainCategory.head C))
        → DependentSplitFunction A (DependentCategory.tail C' x))
      → DependentSplitFunction A C'
  
  -- ### Interface

  dependent-split-function₀
    : {A : Set}
    → {C : ChainCategory zero}
    → {C' : DependentCategory C}
    → DependentSplitFunction A C'
    → SplitFunction A (Category.Object (dependent-category₀ C'))
  dependent-split-function₀ (nil F)
    = F

  dependent-split-function-tail
    : {n : ℕ}
    → {A : Set}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → DependentSplitFunction A C'
    → (x : Category.Object (ChainCategory.head C))
    → DependentSplitFunction A (DependentCategory.tail C' x)
  dependent-split-function-tail (cons F)
    = F

  -- ### Compose

  dependent-split-function-compose
    : {A B : Set}
    → {n : ℕ}
    → {C : ChainCategory n}
    → {C' : DependentCategory C}
    → DependentSplitFunction B C'
    → SplitFunction A B
    → DependentSplitFunction A C'
  dependent-split-function-compose
    {n = zero} F G
    = nil
      (split-function-compose
        (dependent-split-function₀ F) G)
  dependent-split-function-compose
    {n = suc _} F G
    = cons
      (λ x → dependent-split-function-compose
        (dependent-split-function-tail F x) G)

  dependent-split-function-compose'
    : {A : Set}
    → {n : ℕ}
    → {C : ChainCategory n}
    → {C' D' : DependentCategory C}
    → DependentSplitFunctor C' D'
    → DependentSplitFunction A C'
    → DependentSplitFunction A D'
  dependent-split-function-compose'
    {n = zero} F G
    = nil
      (split-function-compose
        (split-functor-base
          (dependent-split-functor₀ F))
        (dependent-split-function₀ G))
  dependent-split-function-compose'
    {n = suc _} F G
    = cons
      (λ x → dependent-split-function-compose'
        (DependentSplitFunctor.tail F x)
        (dependent-split-function-tail G x))

-- ## Modules

DependentSplitFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → Set
  → DependentCategory C
  → Set
DependentSplitFunction
  = Internal.DependentSplitFunction

open Internal.DependentSplitFunction public

open Internal public
  using (dependent-split-function₀; dependent-split-function-compose;
    dependent-split-function-compose')

module DependentSplitFunction where

  open Internal public using () renaming
    ( dependent-split-function-tail
      to tail
    )

