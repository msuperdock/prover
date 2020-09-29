module Prover.Category.Dependent.Simple.Encoding where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Split
  using (DependentSimpleSplitFunctor)
open import Prover.Category.Encoding
  using (Encoding; encoding-comap; encoding-map)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Prelude

-- ## Types

DependentSimpleEncoding
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → Set
  → Set

record DependentSimpleEncoding'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleCategory C)
  (A : Set)
  : Set

-- ## Definitions

DependentSimpleEncoding {n = zero}
  = Encoding
DependentSimpleEncoding {n = suc _}
  = DependentSimpleEncoding'

record DependentSimpleEncoding' {_ C} C' A where

  inductive

  field

    encoding
      : (x : ChainCategory.Object C)
      → DependentSimpleEncoding
        (DependentSimpleCategory.category C' x) A

module DependentSimpleEncoding
  = DependentSimpleEncoding'

-- ## Map

dependent-simple-encoding-map
  : {A : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C' D'
  → DependentSimpleEncoding C' A
  → DependentSimpleEncoding D' A

dependent-simple-encoding-map {n = zero} F e
  = encoding-map F e

dependent-simple-encoding-map {n = suc _} F e
  = record
  { encoding
    = λ x → dependent-simple-encoding-map
      (DependentSimpleSplitFunctor.split-functor F x)
      (DependentSimpleEncoding.encoding e x)
  }

dependent-simple-encoding-comap
  : {A B : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → SplitFunction B A
  → DependentSimpleEncoding C' A
  → DependentSimpleEncoding C' B

dependent-simple-encoding-comap {n = zero} F e
  = encoding-comap F e

dependent-simple-encoding-comap {n = suc _} F e
  = record
  { encoding
    = λ x → dependent-simple-encoding-comap F
      (DependentSimpleEncoding.encoding e x)
  }

