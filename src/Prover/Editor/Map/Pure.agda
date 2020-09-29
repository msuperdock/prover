module Prover.Editor.Map.Pure where

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
  using (DependentInnerEditor; DependentSimpleInnerEditor; EventStack;
    InnerEditor; SimpleInnerEditor; ViewStack)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Prelude

-- ## Editors (dependent)

-- ### DependentInnerEditor

dependent-inner-editor-map-pure
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S P Q : Set}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → SplitFunction Q P
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor V E S Q C'
dependent-inner-editor-map-pure F e
  = record
  { DependentInnerEditor e
  ; pure-encoding
    = dependent-encoding-comap F
      (DependentInnerEditor.pure-encoding e)
  }

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-map-pure
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S P Q : Set}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → SplitFunction Q P
  → DependentSimpleInnerEditor V E S P C'
  → DependentSimpleInnerEditor V E S Q C'
dependent-simple-inner-editor-map-pure F e
  = record
  { DependentSimpleInnerEditor e
  ; pure-encoding
    = dependent-simple-encoding-comap F
      (DependentSimpleInnerEditor.pure-encoding e)
  }

-- ## Editors (nondependent)

-- ### InnerEditor

inner-editor-map-pure
  : {V : ViewStack}
  → {E : EventStack}
  → {S P Q : Set}
  → {C : Category}
  → SplitFunction Q P
  → InnerEditor V E S P C
  → InnerEditor V E S Q C
inner-editor-map-pure
  = dependent-inner-editor-map-pure

-- ### SimpleInnerEditor

simple-inner-editor-map-pure
  : {V : ViewStack}
  → {E : EventStack}
  → {S P Q A : Set}
  → SplitFunction Q P
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor V E S Q A
simple-inner-editor-map-pure
  = dependent-simple-inner-editor-map-pure

