module Prover.Editor.Map.View where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Function
  using (DependentFunction; dependent-function-compose)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Function
  using (DependentSimpleFunction; dependent-simple-function-compose)
open import Prover.Editor
  using (DependentEditor; DependentInnerEditor; DependentSimpleEditor;
    DependentSimpleInnerEditor; DependentSimpleMainEditor;
    DependentSimplePartialEditor; DependentSimpleSplitEditor;
    DependentSplitEditor; Editor; EventStack; InnerEditor; SimpleEditor;
    SimpleInnerEditor; SimpleMainEditor; SimplePartialEditor; SimpleSplitEditor;
    SplitEditor; ViewStack; ViewStackMap; any; view-stack-map-compose-with)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatViewStack; FlatViewStackMap;
    flat-view-stack-map-compose)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Prelude

-- ## Editors (basic)

-- ### Editor

editor-map-view-with
  : {V W : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → (Category.Object C → ViewStackMap V W)
  → Editor V E C
  → Editor W E C
editor-map-view-with F e
  = record
  { Editor e
  ; draw-stack
    = view-stack-map-compose-with F
      (Editor.draw-stack e)
  }

-- ### SimpleEditor

simple-editor-map-view-with
  : {V W : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → (A → ViewStackMap V W)
  → SimpleEditor V E A
  → SimpleEditor W E A
simple-editor-map-view-with F (any e)
  = any (editor-map-view-with F e)
  
simple-editor-map-view
  : {V W : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → ViewStackMap V W
  → SimpleEditor V E A
  → SimpleEditor W E A
simple-editor-map-view F
  = simple-editor-map-view-with (const F)

-- ### FlatEditor

flat-editor-map-view
  : {V W : FlatViewStack}
  → {E : FlatEventStack}
  → {A : Set}
  → FlatViewStackMap V W
  → FlatEditor V E A
  → FlatEditor W E A
flat-editor-map-view F e
  = record
  { FlatEditor e
  ; draw-stack
    = flat-view-stack-map-compose F
      (FlatEditor.draw-stack e)
  }

-- ## Editors (dependent)

-- ### DependentEditor

dependent-editor-map-view-with
  : {n : ℕ}
  → {V W : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentFunction C' (ViewStackMap V W)
  → DependentEditor V E C'
  → DependentEditor W E C'

dependent-editor-map-view-with {n = zero} F e
  = editor-map-view-with F e

dependent-editor-map-view-with {n = suc _} F e
  = record
  { editor
    = λ x → dependent-editor-map-view-with
      (DependentFunction.function F x)
      (DependentEditor.editor e x)
  }

-- ### DependentSplitEditor

module _
  {n : ℕ}
  {V W : ViewStack}
  {E : EventStack}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  dependent-split-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSplitEditor V E C'
    → DependentSplitEditor W E C'
  dependent-split-editor-map-view-with F e
    = record
    { DependentSplitEditor e
    ; editor
      = dependent-editor-map-view-with
        (dependent-function-compose F
          (DependentSplitEditor.bool-function e))
        (DependentSplitEditor.editor e)
    }

  dependent-split-editor-map-view
    : ViewStackMap V W
    → DependentSplitEditor V E C'
    → DependentSplitEditor W E C'
  dependent-split-editor-map-view F
    = dependent-split-editor-map-view-with (const F)

-- ### DependentInnerEditor

module _
  {n : ℕ}
  {V W : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  dependent-inner-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentInnerEditor V E S P C'
    → DependentInnerEditor W E S P C'
  dependent-inner-editor-map-view-with F e
    = record
    { DependentInnerEditor e
    ; editor
      = dependent-editor-map-view-with
        (dependent-function-compose F
          (DependentInnerEditor.bool-function e))
        (DependentInnerEditor.editor e)
    }

  dependent-inner-editor-map-view
    : ViewStackMap V W
    → DependentInnerEditor V E S P C'
    → DependentInnerEditor W E S P C'
  dependent-inner-editor-map-view F
    = dependent-inner-editor-map-view-with (const F)

-- ### DependentSimpleEditor

dependent-simple-editor-map-view-with
  : {n : ℕ}
  → {V W : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleFunction C' (ViewStackMap V W)
  → DependentSimpleEditor V E C'
  → DependentSimpleEditor W E C'

dependent-simple-editor-map-view-with {n = zero} F e
  = simple-editor-map-view-with F e

dependent-simple-editor-map-view-with {n = suc _} F e
  = record
  { editor
    = λ x → dependent-simple-editor-map-view-with
      (DependentSimpleFunction.function F x)
      (DependentSimpleEditor.editor e x)
  }

-- ### DependentSimplePartialEditor

module _
  {n : ℕ}
  {V W : ViewStack}
  {E : EventStack}
  {C : ChainCategory n}
  {C' : DependentSet C}
  where

  dependent-simple-partial-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSimplePartialEditor V E C'
    → DependentSimplePartialEditor W E C'
  dependent-simple-partial-editor-map-view-with F e
    = record
    { DependentSimplePartialEditor e
    ; editor
      = dependent-simple-editor-map-view-with
        (dependent-simple-function-compose F
          (DependentSimplePartialEditor.bool-function e))
        (DependentSimplePartialEditor.editor e)
    }

  dependent-simple-partial-editor-map-view
    : ViewStackMap V W
    → DependentSimplePartialEditor V E C'
    → DependentSimplePartialEditor W E C'
  dependent-simple-partial-editor-map-view F
    = dependent-simple-partial-editor-map-view-with (const F)

-- ### DependentSimpleSplitEditor

module _
  {n : ℕ}
  {V W : ViewStack}
  {E : EventStack}
  {C : ChainCategory n}
  {C' : DependentSimpleCategory C}
  where

  dependent-simple-split-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSimpleSplitEditor V E C'
    → DependentSimpleSplitEditor W E C'
  dependent-simple-split-editor-map-view-with F e
    = record
    { DependentSimpleSplitEditor e
    ; editor
      = dependent-simple-editor-map-view-with
        (dependent-simple-function-compose F
          (DependentSimpleSplitEditor.bool-function e))
        (DependentSimpleSplitEditor.editor e)
    }

  dependent-simple-split-editor-map-view
    : ViewStackMap V W
    → DependentSimpleSplitEditor V E C'
    → DependentSimpleSplitEditor W E C'
  dependent-simple-split-editor-map-view F
    = dependent-simple-split-editor-map-view-with (const F)

-- ### DependentSimpleMainEditor

module _
  {n : ℕ}
  {V W : ViewStack}
  {E : EventStack}
  {S : Set}
  {C : ChainCategory n}
  where

  dependent-simple-main-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSimpleMainEditor V E S C
    → DependentSimpleMainEditor W E S C
  dependent-simple-main-editor-map-view-with F e
    = record
    { DependentSimpleMainEditor e
    ; editor
      = dependent-simple-editor-map-view-with
        (dependent-simple-function-compose F
          (DependentSimpleMainEditor.bool-function e))
        (DependentSimpleMainEditor.editor e)
    }

  dependent-simple-main-editor-map-view
    : ViewStackMap V W
    → DependentSimpleMainEditor V E S C
    → DependentSimpleMainEditor W E S C
  dependent-simple-main-editor-map-view F
    = dependent-simple-main-editor-map-view-with (const F)

-- ### DependentSimpleInnerEditor

module _
  {n : ℕ}
  {V W : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C : ChainCategory n}
  {C' : DependentSimpleCategory C}
  where

  dependent-simple-inner-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → DependentSimpleInnerEditor V E S P C'
    → DependentSimpleInnerEditor W E S P C'
  dependent-simple-inner-editor-map-view-with F e
    = record
    { DependentSimpleInnerEditor e
    ; editor
      = dependent-simple-editor-map-view-with
        (dependent-simple-function-compose F
          (DependentSimpleInnerEditor.bool-function e))
        (DependentSimpleInnerEditor.editor e)
    }

  dependent-simple-inner-editor-map-view
    : ViewStackMap V W
    → DependentSimpleInnerEditor V E S P C'
    → DependentSimpleInnerEditor W E S P C'
  dependent-simple-inner-editor-map-view F
    = dependent-simple-inner-editor-map-view-with (const F)

-- ## Editors (nondependent)

-- ### SplitEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {C : Category}
  where

  split-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SplitEditor V E C
    → SplitEditor W E C
  split-editor-map-view-with
    = dependent-split-editor-map-view-with

  split-editor-map-view
    : ViewStackMap V W
    → SplitEditor V E C
    → SplitEditor W E C
  split-editor-map-view
    = dependent-split-editor-map-view

-- ### InnerEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C : Category}
  where

  inner-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → InnerEditor V E S P C
    → InnerEditor W E S P C
  inner-editor-map-view-with
    = dependent-inner-editor-map-view-with

  inner-editor-map-view
    : ViewStackMap V W
    → InnerEditor V E S P C
    → InnerEditor W E S P C
  inner-editor-map-view
    = dependent-inner-editor-map-view

-- ### SimplePartialEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  simple-partial-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SimplePartialEditor V E A
    → SimplePartialEditor W E A
  simple-partial-editor-map-view-with
    = dependent-simple-partial-editor-map-view-with

  simple-partial-editor-map-view
    : ViewStackMap V W
    → SimplePartialEditor V E A
    → SimplePartialEditor W E A
  simple-partial-editor-map-view
    = dependent-simple-partial-editor-map-view

-- ### SimpleSplitEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  simple-split-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SimpleSplitEditor V E A
    → SimpleSplitEditor W E A
  simple-split-editor-map-view-with
    = dependent-simple-split-editor-map-view-with

  simple-split-editor-map-view
    : ViewStackMap V W
    → SimpleSplitEditor V E A
    → SimpleSplitEditor W E A
  simple-split-editor-map-view
    = dependent-simple-split-editor-map-view

-- ### SimpleMainEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S : Set}
  where

  simple-main-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SimpleMainEditor V E S
    → SimpleMainEditor W E S
  simple-main-editor-map-view-with
    = dependent-simple-main-editor-map-view-with

  simple-main-editor-map-view
    : ViewStackMap V W
    → SimpleMainEditor V E S
    → SimpleMainEditor W E S
  simple-main-editor-map-view
    = dependent-simple-main-editor-map-view

-- ### SimpleInnerEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S P A : Set}
  where

  simple-inner-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SimpleInnerEditor V E S P A
    → SimpleInnerEditor W E S P A
  simple-inner-editor-map-view-with
    = dependent-simple-inner-editor-map-view-with

  simple-inner-editor-map-view
    : ViewStackMap V W
    → SimpleInnerEditor V E S P A
    → SimpleInnerEditor W E S P A
  simple-inner-editor-map-view
    = dependent-simple-inner-editor-map-view

