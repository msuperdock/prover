module Prover.Category.Dependent.Encoding where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Encoding
  using (Encoding; encoding-comap; encoding-map)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Prelude

-- ## Types

DependentEncoding
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → Set
  → Set

record DependentEncoding'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentCategory C)
  (A : Set)
  : Set

-- ## Definitions

DependentEncoding {n = zero} C'
  = Encoding (Category.Object C')
DependentEncoding {n = suc _} C'
  = DependentEncoding' C'

record DependentEncoding' {_ C} C' A where

  inductive

  field

    encoding
      : (x : ChainCategory.Object C)
      → DependentEncoding
        (DependentCategory.category C' x) A

module DependentEncoding
  = DependentEncoding'

-- ## Map

dependent-encoding-map
  : {A : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → DependentSplitFunctor C' D'
  → DependentEncoding C' A
  → DependentEncoding D' A

dependent-encoding-map {n = zero} F e
  = encoding-map (SplitFunctor.split-function F) e

dependent-encoding-map {n = suc _} F e
  = record 
  { encoding
    = λ x → dependent-encoding-map
      (DependentSplitFunctor.split-functor F x)
      (DependentEncoding.encoding e x)
  }

dependent-encoding-comap
  : {A B : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → SplitFunction B A
  → DependentEncoding C' A
  → DependentEncoding C' B

dependent-encoding-comap {n = zero} F e
  = encoding-comap F e

dependent-encoding-comap {n = suc _} F e
  = record
  { encoding
    = λ x → dependent-encoding-comap F
      (DependentEncoding.encoding e x)
  }

