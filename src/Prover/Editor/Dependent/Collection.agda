module Prover.Editor.Dependent.Collection where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Collection
  using (dependent-category-collection)
open import Prover.Category.Dependent.Decidable
  using (DependentDecidable)
open import Prover.Category.Dependent.Relation
  using (DependentRelation)
open import Prover.Category.Dependent.Split.Collection
  using (dependent-split-functor-collection)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Dependent
  using (DependentPartialEditor; DependentSplitEditor; DependentSplitMainEditor)
open import Prover.Editor.Dependent.List
  using (dependent-partial-editor-list; dependent-split-editor-list;
    dependent-split-main-editor-list)
open import Prover.Editor.Dependent.Map
  using (dependent-partial-editor-map; dependent-split-editor-map;
    dependent-split-main-editor-map)
open import Prover.Editor.List
  using (event-stack-list; view-stack-list)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Collection
  using (dependent-set-collection)
open import Prover.Function.Dependent.Simple.Decidable
  using (DependentSimpleDecidable)
open import Prover.Function.Dependent.Simple.Partial.Collection
  using (dependent-simple-partial-function-collection)
open import Prover.Function.Dependent.Simple.Relation
  using (DependentSimpleRelation)
open import Prover.Prelude

-- ## DependentPartialEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentSet C}
  {R : DependentSimpleRelation C'}
  where

  dependent-partial-editor-collection
    : DependentSimpleDecidable R
    → Direction
    → DependentPartialEditor V E C'
    → DependentPartialEditor
      (view-stack-list V)
      (event-stack-list E)
      (dependent-set-collection R)
  dependent-partial-editor-collection d d'
    = dependent-partial-editor-map
      (dependent-simple-partial-function-collection d)
    ∘ dependent-partial-editor-list d'

-- ## DependentSplitEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  {R : DependentRelation C'}
  where

  dependent-split-editor-collection
    : DependentDecidable R
    → Direction
    → DependentSplitEditor V E C'
    → DependentSplitEditor
      (view-stack-list V)
      (event-stack-list E)
      (dependent-category-collection R)
  dependent-split-editor-collection d d'
    = dependent-split-editor-map (dependent-split-functor-collection d)
    ∘ dependent-split-editor-list d'

-- ## DependentSplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  {R : DependentRelation C'}
  where

  dependent-split-main-editor-collection
    : DependentDecidable R
    → Direction
    → DependentSplitMainEditor V E S P C'
    → DependentSplitMainEditor
      (view-stack-list V)
      (event-stack-list E)
      (List S)
      (List P)
      (dependent-category-collection R)
  dependent-split-main-editor-collection d d'
    = dependent-split-main-editor-map (dependent-split-functor-collection d)
    ∘ dependent-split-main-editor-list d'

