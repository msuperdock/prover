module Prover.Editor.Collection.Unit where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Collection.Unit
  using (category-collection-unit)
open import Prover.Category.Dependent.Collection.Unit
  using (dependent-category-collection-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Decidable
  using (DependentSimpleDecidable)
open import Prover.Category.Dependent.Simple.Relation
  using (DependentSimpleRelation)
open import Prover.Category.Dependent.Split.Collection.Unit
  using (dependent-split-functor-collection-unit)
open import Prover.Editor
  using (DependentInnerEditor; DependentSimpleInnerEditor;
    DependentSimpleSplitEditor; DependentSplitEditor; EventStack; InnerEditor;
    SimpleInnerEditor; SimpleSplitEditor; SplitEditor; ViewStack)
open import Prover.Editor.List
  using (event-stack-list; view-stack-list)
open import Prover.Editor.List.Unit
  using (dependent-inner-editor-list-unit; dependent-split-editor-list-unit)
open import Prover.Editor.Map
  using (dependent-inner-editor-map; dependent-split-editor-map)
open import Prover.Prelude

-- ## Editors (dependent)

-- ### DependentSplitEditor

-- Takes direction from earlier to later elements.
dependent-split-editor-collection-unit
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → Direction
  → DependentSimpleSplitEditor V E C'
  → DependentSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-category-collection-unit R)
dependent-split-editor-collection-unit d d'
  = dependent-split-editor-map (dependent-split-functor-collection-unit d)
  ∘ dependent-split-editor-list-unit d'

-- ### DependentInnerEditor

-- Takes direction from earlier to later elements.
dependent-inner-editor-collection-unit
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → Direction
  → DependentSimpleInnerEditor V E S P C'
  → DependentInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-category-collection-unit R)
dependent-inner-editor-collection-unit d d'
  = dependent-inner-editor-map (dependent-split-functor-collection-unit d)
  ∘ dependent-inner-editor-list-unit d'

-- ## Editors (nondependent)

-- ### SplitEditor

-- Takes direction from earlier to later elements.
split-editor-collection-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → (R : Relation A)
  → Decidable R
  → Direction
  → SimpleSplitEditor V E A
  → SplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (category-collection-unit R)
split-editor-collection-unit _
  = dependent-split-editor-collection-unit

-- ### InnerEditor

-- Takes direction from earlier to later elements.
inner-editor-collection-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A : Set}
  → (R : Relation A)
  → Decidable R
  → Direction
  → SimpleInnerEditor V E S P A
  → InnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (category-collection-unit R)
inner-editor-collection-unit _
  = dependent-inner-editor-collection-unit

