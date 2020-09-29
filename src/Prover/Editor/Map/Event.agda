module Prover.Editor.Map.Event where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Editor
  using (DependentEditor; DependentInnerEditor; DependentSimpleEditor;
    DependentSimpleInnerEditor; DependentSimpleMainEditor;
    DependentSimplePartialEditor; DependentSimpleSplitEditor;
    DependentSplitEditor; Editor; EventStack; EventStackMap; InnerEditor;
    SimpleEditor; SimpleInnerEditor; SimpleMainEditor; SimplePartialEditor;
    SimpleSplitEditor; SplitEditor; ViewStack; any)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatEventStackMap; FlatViewStack)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Prelude

-- ## Editors (basic)

-- ### Editor

editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {C : Category}
  → EventStackMap E F
  → Editor V E C
  → Editor V F C
editor-map-event G e
  = record
  { Editor e
  ; mode
    = λ s sp → EventStackMap.mode G
      (Editor.mode e s sp)
  ; mode-inner
    = λ s sp s' sp' → EventStackMap.mode-inner G
      (Editor.mode-inner e s sp s' sp')
  ; handle
    = λ s sp e' → Editor.handle e s sp
      (EventStackMap.event G (Editor.mode e s sp) e')
  ; handle-inner
    = λ s sp s' sp' e' → Editor.handle-inner e s sp s' sp'
      (EventStackMap.event-inner G (Editor.mode-inner e s sp s' sp') e')
  }

-- ### SimpleEditor

simple-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {A : Set}
  → EventStackMap E F
  → SimpleEditor V E A
  → SimpleEditor V F A
simple-editor-map-event G (any e)
  = any (editor-map-event G e)

-- ### FlatEditor

flat-editor-map-event
  : {V : FlatViewStack}
  → {E F : FlatEventStack}
  → {A : Set}
  → FlatEventStackMap E F
  → FlatEditor V E A
  → FlatEditor V F A
flat-editor-map-event G e
  = record
  { FlatEditor e
  ; mode
    = λ s sp → FlatEventStackMap.mode G
      (FlatEditor.mode e s sp)
  ; handle
    = λ s sp e' → FlatEditor.handle e s sp
      (FlatEventStackMap.event G (FlatEditor.mode e s sp) e')
  }

-- ## Editors (dependent)

-- ### DependentEditor

dependent-editor-map-event
  : {n : ℕ}
  → {V : ViewStack}
  → {E F : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → EventStackMap E F
  → DependentEditor V E C'
  → DependentEditor V F C'

dependent-editor-map-event {n = zero} G e
  = editor-map-event G e

dependent-editor-map-event {n = suc _} G e
  = record
  { editor
    = λ x → dependent-editor-map-event G
      (DependentEditor.editor e x)
  }

-- ### DependentSplitEditor

dependent-split-editor-map-event
  : {n : ℕ}
  → {V : ViewStack}
  → {E F : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → EventStackMap E F
  → DependentSplitEditor V E C'
  → DependentSplitEditor V F C'
dependent-split-editor-map-event G e
  = record
  { DependentSplitEditor e
  ; editor
    = dependent-editor-map-event G
      (DependentSplitEditor.editor e)
  }

-- ### DependentInnerEditor

dependent-inner-editor-map-event
  : {n : ℕ}
  → {V : ViewStack}
  → {E F : EventStack}
  → {S P : Set}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → EventStackMap E F
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor V F S P C'
dependent-inner-editor-map-event G e
  = record
  { DependentInnerEditor e
  ; editor
    = dependent-editor-map-event G
      (DependentInnerEditor.editor e)
  }

-- ### DependentSimpleEditor

dependent-simple-editor-map-event
  : {n : ℕ}
  → {V : ViewStack}
  → {E F : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → EventStackMap E F
  → DependentSimpleEditor V E C'
  → DependentSimpleEditor V F C'

dependent-simple-editor-map-event {n = zero} G e
  = simple-editor-map-event G e

dependent-simple-editor-map-event {n = suc _} G e
  = record
  { editor
    = λ x → dependent-simple-editor-map-event G
      (DependentSimpleEditor.editor e x)
  }

-- ### DependentSimplePartialEditor

dependent-simple-partial-editor-map-event
  : {n : ℕ}
  → {V : ViewStack}
  → {E F : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → EventStackMap E F
  → DependentSimplePartialEditor V E C'
  → DependentSimplePartialEditor V F C'
dependent-simple-partial-editor-map-event G e
  = record
  { DependentSimplePartialEditor e
  ; editor
    = dependent-simple-editor-map-event G
      (DependentSimplePartialEditor.editor e)
  }

-- ### DependentSimpleSplitEditor

dependent-simple-split-editor-map-event
  : {n : ℕ}
  → {V : ViewStack}
  → {E F : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → EventStackMap E F
  → DependentSimpleSplitEditor V E C'
  → DependentSimpleSplitEditor V F C'
dependent-simple-split-editor-map-event G e
  = record
  { DependentSimpleSplitEditor e
  ; editor
    = dependent-simple-editor-map-event G
      (DependentSimpleSplitEditor.editor e)
  }

-- ### DependentSimpleMainEditor

dependent-simple-main-editor-map-event
  : {n : ℕ}
  → {V : ViewStack}
  → {E F : EventStack}
  → {S : Set}
  → {C : ChainCategory n}
  → EventStackMap E F
  → DependentSimpleMainEditor V E S C
  → DependentSimpleMainEditor V F S C
dependent-simple-main-editor-map-event G e
  = record
  { DependentSimpleMainEditor e
  ; editor
    = dependent-simple-editor-map-event G
      (DependentSimpleMainEditor.editor e)
  }

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-map-event
  : {n : ℕ}
  → {V : ViewStack}
  → {E F : EventStack}
  → {S P : Set}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → EventStackMap E F
  → DependentSimpleInnerEditor V E S P C'
  → DependentSimpleInnerEditor V F S P C'
dependent-simple-inner-editor-map-event G e
  = record
  { DependentSimpleInnerEditor e
  ; editor
    = dependent-simple-editor-map-event G
      (DependentSimpleInnerEditor.editor e)
  }

-- ## Editors (nondependent)

-- ### SplitEditor

split-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {C : Category}
  → EventStackMap E F
  → SplitEditor V E C
  → SplitEditor V F C
split-editor-map-event
  = dependent-split-editor-map-event

-- ### InnerEditor

inner-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {S P : Set}
  → {C : Category}
  → EventStackMap E F
  → InnerEditor V E S P C
  → InnerEditor V F S P C
inner-editor-map-event
  = dependent-inner-editor-map-event

-- ### SimplePartialEditor

simple-partial-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {A : Set}
  → EventStackMap E F
  → SimplePartialEditor V E A
  → SimplePartialEditor V F A
simple-partial-editor-map-event
  = dependent-simple-partial-editor-map-event

-- ### SimpleSplitEditor

simple-split-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {A : Set}
  → EventStackMap E F
  → SimpleSplitEditor V E A
  → SimpleSplitEditor V F A
simple-split-editor-map-event
  = dependent-simple-split-editor-map-event

-- ### SimpleMainEditor

simple-main-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {S : Set}
  → EventStackMap E F
  → SimpleMainEditor V E S
  → SimpleMainEditor V F S
simple-main-editor-map-event
  = dependent-simple-main-editor-map-event

-- ### SimpleInnerEditor

simple-inner-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {S P A : Set}
  → EventStackMap E F
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor V F S P A
simple-inner-editor-map-event
  = dependent-simple-inner-editor-map-event

