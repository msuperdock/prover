module Prover.Editor.Collection where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Collection
  using (category-collection)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Collection
  using (dependent-category-collection)
open import Prover.Category.Dependent.Decidable
  using (DependentDecidable)
open import Prover.Category.Dependent.Relation
  using (DependentRelation)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Collection
  using (dependent-simple-category-collection)
open import Prover.Category.Dependent.Simple.Decidable
  using (DependentSimpleDecidable)
open import Prover.Category.Dependent.Simple.Relation
  using (DependentSimpleRelation)
open import Prover.Category.Dependent.Simple.Split.Collection
  using (dependent-simple-split-functor-collection)
open import Prover.Category.Dependent.Split.Collection
  using (dependent-split-functor-collection)
open import Prover.Editor
  using (DependentInnerEditor; DependentSimpleInnerEditor;
    DependentSimplePartialEditor; DependentSimpleSplitEditor;
    DependentSplitEditor; EventStack; InnerEditor; SimpleInnerEditor;
    SimplePartialEditor; SimpleSplitEditor; SplitEditor; ViewStack)
open import Prover.Editor.List
  using (event-stack-list; dependent-inner-editor-list;
    dependent-simple-inner-editor-list; dependent-simple-partial-editor-list;
    dependent-simple-split-editor-list; dependent-split-editor-list;
    view-stack-list)
open import Prover.Editor.Map
  using (dependent-inner-editor-map; dependent-simple-inner-editor-map;
    dependent-simple-partial-editor-map; dependent-simple-split-editor-map;
    dependent-split-editor-map)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Collection
  using (dependent-set-collection)
open import Prover.Function.Dependent.Decidable using ()
  renaming (DependentDecidable to DependentDecidable')
open import Prover.Function.Dependent.Partial.Collection
  using (dependent-partial-function-collection)
open import Prover.Function.Dependent.Relation using ()
  renaming (DependentRelation to DependentRelation')
open import Prover.Prelude

-- ## Editors (dependent)

-- ### DependentSplitEditor

dependent-split-editor-collection
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → DependentDecidable R
  → Direction
  → DependentSplitEditor V E C'
  → DependentSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-category-collection R)
dependent-split-editor-collection d d'
  = dependent-split-editor-map (dependent-split-functor-collection d)
  ∘ dependent-split-editor-list d'

-- ### DependentInnerEditor

dependent-inner-editor-collection
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → DependentDecidable R
  → Direction
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-category-collection R)
dependent-inner-editor-collection d d'
  = dependent-inner-editor-map (dependent-split-functor-collection d)
  ∘ dependent-inner-editor-list d'

-- ### DependentSimplePartialEditor

dependent-simple-partial-editor-collection
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → {R : DependentRelation' C'}
  → DependentDecidable' R
  → Direction
  → DependentSimplePartialEditor V E C'
  → DependentSimplePartialEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-set-collection R)
dependent-simple-partial-editor-collection d d'
  = dependent-simple-partial-editor-map
    (dependent-partial-function-collection d)
  ∘ dependent-simple-partial-editor-list d'

-- ### DependentSimpleSplitEditor

dependent-simple-split-editor-collection
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → Direction
  → DependentSimpleSplitEditor V E C'
  → DependentSimpleSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-simple-category-collection R)
dependent-simple-split-editor-collection d d'
  = dependent-simple-split-editor-map
    (dependent-simple-split-functor-collection d)
  ∘ dependent-simple-split-editor-list d'

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-collection
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
  → DependentSimpleInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (dependent-simple-category-collection R)
dependent-simple-inner-editor-collection d d'
  = dependent-simple-inner-editor-map
    (dependent-simple-split-functor-collection d)
  ∘ dependent-simple-inner-editor-list d'

-- ## Editors (nondependent)

-- ### SplitEditor

-- Takes direction from earlier to later elements.
split-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → (R : Relation (Category.Object C))
  → Decidable R
  → Direction
  → SplitEditor V E C
  → SplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (category-collection C R)
split-editor-collection _
  = dependent-split-editor-collection

-- ### InnerEditor

-- Takes direction from earlier to later elements.
inner-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : Category}
  → (R : Relation (Category.Object C))
  → Decidable R
  → Direction
  → InnerEditor V E S P C
  → InnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (category-collection C R)
inner-editor-collection _
  = dependent-inner-editor-collection

-- ### SimplePartialEditor

-- Takes direction from earlier to later elements.
simple-partial-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → (R : Relation A)
  → Decidable R
  → Direction
  → SimplePartialEditor V E A
  → SimplePartialEditor
    (view-stack-list V)
    (event-stack-list E)
    (Collection R)
simple-partial-editor-collection _
  = dependent-simple-partial-editor-collection

-- ### SimpleSplitEditor

-- Takes direction from earlier to later elements.
simple-split-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → (R : Relation A)
  → Decidable R
  → Direction
  → SimpleSplitEditor V E A
  → SimpleSplitEditor
    (view-stack-list V)
    (event-stack-list E)
    (Collection R)
simple-split-editor-collection _
  = dependent-simple-split-editor-collection

-- ### SimpleInnerEditor

-- Takes direction from earlier to later elements.
simple-inner-editor-collection
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A : Set}
  → (R : Relation A)
  → Decidable R
  → Direction
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor
    (view-stack-list V)
    (event-stack-list E)
    (List S)
    (List P)
    (Collection R)
simple-inner-editor-collection _
  = dependent-simple-inner-editor-collection

