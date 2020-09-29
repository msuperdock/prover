module Prover.Category.Dependent.Simple.Split.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Product
  using (dependent-simple-category-product)
open import Prover.Category.Dependent.Simple.Split
  using (DependentSimpleSplitFunctor)
open import Prover.Category.Dependent.Simple.Split.Convert
  using (dependent-split-functor-simple)
open import Prover.Category.Dependent.Split.Product
  using (dependent-split-functor-product)
open import Prover.Category.Dependent.Split.Unit
  using (dependent-split-functor-unit)
open import Prover.Prelude

-- ## DependentSimpleSplitFunctor

dependent-simple-split-functor-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' D₁' D₂' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C₁' D₁'
  → DependentSimpleSplitFunctor C₂' D₂'
  → DependentSimpleSplitFunctor
    (dependent-simple-category-product C₁' C₂')
    (dependent-simple-category-product D₁' D₂')
dependent-simple-split-functor-product F₁ F₂
  = dependent-split-functor-simple
  $ dependent-split-functor-product
    (dependent-split-functor-unit F₁)
    (dependent-split-functor-unit F₂)

