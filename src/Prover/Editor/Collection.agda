module Prover.Editor.Collection where

open import Prover.Category
  using (Category)
open import Prover.Category.Collection
  using (category-collection)
open import Prover.Category.Split.Collection
  using (split-functor-collection)
open import Prover.Editor
  using (EventStack; PartialEditor; SplitEditor; SplitMainEditor; ViewStack)
open import Prover.Editor.List
  using (event-stack-list; partial-editor-list; split-editor-list;
    split-main-editor-list; view-stack-list)
open import Prover.Editor.Map
  using (partial-editor-map; split-editor-map; split-main-editor-map)
open import Prover.Prelude

-- ## Editors

-- ### PartialEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  -- Takes direction from earlier to later elements.
  partial-editor-collection
    : Direction
    → (R : Relation A)
    → Decidable R
    → PartialEditor V E A
    → PartialEditor
      (view-stack-list V)
      (event-stack-list E)
      (Collection R)
  partial-editor-collection d R d'
    = partial-editor-map (Collection.from-list R d')
    ∘ partial-editor-list d

-- ### SplitEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {C : Category}
  where

  -- Takes direction from earlier to later elements.
  split-editor-collection
    : Direction
    → (R : Relation (Category.Object C))
    → Decidable R
    → SplitEditor V E C
    → SplitEditor
      (view-stack-list V)
      (event-stack-list E)
      (category-collection C R)
  split-editor-collection d R d'
    = split-editor-map (split-functor-collection C R d')
    ∘ split-editor-list d

-- ### SplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C : Category}
  where

  -- Takes direction from earlier to later elements.
  split-main-editor-collection
    : Direction
    → (R : Relation (Category.Object C))
    → Decidable R
    → SplitMainEditor V E S P C
    → SplitMainEditor
      (view-stack-list V)
      (event-stack-list E)
      (List S)
      (List P)
      (category-collection C R)
  split-main-editor-collection d R d'
    = split-main-editor-map (split-functor-collection C R d')
    ∘ split-main-editor-list d

