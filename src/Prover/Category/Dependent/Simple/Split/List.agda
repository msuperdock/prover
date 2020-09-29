module Prover.Category.Dependent.Simple.Split.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.List
  using (dependent-simple-category-list)
open import Prover.Category.Dependent.Simple.Split
  using (DependentSimpleSplitFunctor)
open import Prover.Category.Dependent.Simple.Split.Convert
  using (dependent-split-functor-simple)
open import Prover.Category.Dependent.Split.List
  using (dependent-split-functor-list)
open import Prover.Category.Dependent.Split.Unit
  using (dependent-split-functor-unit)
open import Prover.Prelude

-- ## DependentSimpleSplitFunctor

dependent-simple-split-functor-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C' D'
  → DependentSimpleSplitFunctor
    (dependent-simple-category-list C')
    (dependent-simple-category-list D')
dependent-simple-split-functor-list F
  = dependent-split-functor-simple
  $ dependent-split-functor-list
    (dependent-split-functor-unit F)

