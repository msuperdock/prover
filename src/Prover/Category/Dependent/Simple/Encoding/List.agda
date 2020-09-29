module Prover.Category.Dependent.Simple.Encoding.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Encoding.List
  using (dependent-encoding-list)
open import Prover.Category.Dependent.Encoding.Unit
  using (dependent-encoding-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Encoding
  using (DependentSimpleEncoding)
open import Prover.Category.Dependent.Simple.Encoding.Convert
  using (dependent-encoding-simple)
open import Prover.Category.Dependent.Simple.List
  using (dependent-simple-category-list)
open import Prover.Prelude

-- ## DependentSimpleEncoding

dependent-simple-encoding-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {A : Set}
  → DependentSimpleEncoding C' A
  → DependentSimpleEncoding
    (dependent-simple-category-list C')
    (List A)
dependent-simple-encoding-list e
  = dependent-encoding-simple
  $ dependent-encoding-list
    (dependent-encoding-unit e)

