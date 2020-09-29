module Prover.Editor.Map.State where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding
  using (dependent-encoding-comap)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Encoding
  using (dependent-simple-encoding-comap)
open import Prover.Editor
  using (DependentInnerEditor; DependentSimpleInnerEditor;
    DependentSimpleMainEditor; EventStack; InnerEditor; SimpleInnerEditor;
    SimpleMainEditor; ViewStack)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Prelude

-- ## Editors (dependent)

-- ### DependentInnerEditor

dependent-inner-editor-map-state
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S T P : Set}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → SplitFunction T S
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor V E T P C'
dependent-inner-editor-map-state F e
  = record
  { DependentInnerEditor e
  ; state-encoding
    = dependent-encoding-comap F
      (DependentInnerEditor.state-encoding e)
  }

-- ### DependentSimpleMainEditor

dependent-simple-main-editor-map-state
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S T : Set}
  → {C : ChainCategory n}
  → SplitFunction T S
  → DependentSimpleMainEditor V E S C
  → DependentSimpleMainEditor V E T C
dependent-simple-main-editor-map-state F e
  = record
  { DependentSimpleMainEditor e
  ; state-encoding
    = dependent-simple-encoding-comap F
      (DependentSimpleMainEditor.state-encoding e)
  }

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-map-state
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S T P : Set}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → SplitFunction T S
  → DependentSimpleInnerEditor V E S P C'
  → DependentSimpleInnerEditor V E T P C'
dependent-simple-inner-editor-map-state F e
  = record
  { DependentSimpleInnerEditor e
  ; state-encoding
    = dependent-simple-encoding-comap F
      (DependentSimpleInnerEditor.state-encoding e)
  }

-- ## Editors (nondependent)

-- ### InnerEditor

inner-editor-map-state
  : {V : ViewStack}
  → {E : EventStack}
  → {S T P : Set}
  → {C : Category}
  → SplitFunction T S
  → InnerEditor V E S P C
  → InnerEditor V E T P C
inner-editor-map-state
  = dependent-inner-editor-map-state

-- ### SimpleMainEditor

simple-main-editor-map-state
  : {V : ViewStack}
  → {E : EventStack}
  → {S T : Set}
  → SplitFunction T S
  → SimpleMainEditor V E S
  → SimpleMainEditor V E T
simple-main-editor-map-state
  = dependent-simple-main-editor-map-state

-- ### SimpleInnerEditor

simple-inner-editor-map-state
  : {V : ViewStack}
  → {E : EventStack}
  → {S T P A : Set}
  → SplitFunction T S
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor V E T P A
simple-inner-editor-map-state
  = dependent-simple-inner-editor-map-state

