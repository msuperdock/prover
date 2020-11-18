module Prover.Editor.List.Unit where

open import Prover.Category.List.Unit
  using (category-list-unit)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.List.Unit
  using (dependent-category-list-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Split.List.Unit
  using (dependent-split-functor-list-unit)
open import Prover.Editor
  using (DependentInnerEditor; DependentSimpleInnerEditor;
    DependentSimpleSplitEditor; DependentSplitEditor; EventStack; InnerEditor;
    SimpleInnerEditor; SimpleSplitEditor; SplitEditor; ViewStack)
open import Prover.Editor.List
  using (dependent-inner-editor-list; dependent-split-editor-list;
    event-stack-list; view-stack-list)
open import Prover.Editor.Map
  using (dependent-inner-editor-map; dependent-split-editor-map)
open import Prover.Editor.Unit
  using (dependent-inner-editor-unit; dependent-split-editor-unit)
open import Prover.Prelude

-- ## Editors (dependent)

-- ### DependentSplitEditor

-- Takes direction from earlier to later elements.
dependent-split-editor-list-unit
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleSplitEditor V E C'
  → DependentSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-category-list-unit C')
dependent-split-editor-list-unit {C' = C'} d
  = dependent-split-editor-map (dependent-split-functor-list-unit C')
  ∘ dependent-split-editor-list d
  ∘ dependent-split-editor-unit

-- ### DependentInnerEditor

-- Takes direction from earlier to later elements.
dependent-inner-editor-list-unit
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleInnerEditor V E S P C'
  → DependentInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-category-list-unit C')
dependent-inner-editor-list-unit {C' = C'} d
  = dependent-inner-editor-map (dependent-split-functor-list-unit C')
  ∘ dependent-inner-editor-list d
  ∘ dependent-inner-editor-unit

-- ## Editors (nondependent)

-- ### SplitEditor

-- Takes direction from earlier to later elements.
split-editor-list-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → Direction
  → SimpleSplitEditor V E A
  → SplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (category-list-unit A)
split-editor-list-unit
  = dependent-split-editor-list-unit

-- ### InnerEditor

-- Takes direction from earlier to later elements.
inner-editor-list-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A : Set}
  → Direction
  → SimpleInnerEditor V E S P A
  → InnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (category-list-unit A)
inner-editor-list-unit
  = dependent-inner-editor-list-unit

