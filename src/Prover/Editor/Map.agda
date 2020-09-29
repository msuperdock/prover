module Prover.Editor.Map where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding
  using (dependent-encoding-map)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Encoding
  using (dependent-simple-encoding-map)
open import Prover.Category.Dependent.Simple.Partial
  using (dependent-simple-partial-function-compose)
open import Prover.Category.Dependent.Simple.Split
  using (DependentSimpleSplitFunctor; dependent-simple-split-functor-compose)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; dependent-split-functor-compose)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Editor
  using (DependentInnerEditor; DependentSimpleInnerEditor;
    DependentSimplePartialEditor; DependentSimpleSplitEditor;
    DependentSplitEditor; EventStack; InnerEditor; SimpleInnerEditor;
    SimplePartialEditor; SimpleSplitEditor; SplitEditor; ViewStack)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatViewStack)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Partial
  using (DependentPartialFunction)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Prelude

-- ## Editors (basic)

-- ### FlatEditor

module _
  {V : FlatViewStack}
  {E : FlatEventStack}
  {A B : Set}
  where

  module FlatEditorMap
    (f : A → Maybe B)
    (e : FlatEditor V E A)
    where

    open FlatEditor e public
      hiding (handle-return)

    handle-return
      : (s : State)
      → StatePath s
      → B ⊔ Σ State StatePath
    handle-return s sp
      with FlatEditor.handle-return e s sp
    ... | ι₂ s'
      = ι₂ s'
    ... | ι₁ x
      with f x
    ... | nothing
      = ι₂ (s , sp)
    ... | just y
      = ι₁ y

  flat-editor-map
    : (A → Maybe B)
    → FlatEditor V E A
    → FlatEditor V E B
  flat-editor-map f e
    = record {FlatEditorMap f e}

-- ## Editors (dependent)

-- ### DependentSplitEditor

dependent-split-editor-map
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → DependentSplitFunctor C' D'
  → DependentSplitEditor V E C'
  → DependentSplitEditor V E D'
dependent-split-editor-map F e
  = record
  { DependentSplitEditor e
  ; split-functor
    = dependent-split-functor-compose F
      (DependentSplitEditor.split-functor e)
  }

-- ### DependentInnerEditor

dependent-inner-editor-map
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → DependentSplitFunctor C' D'
  → DependentInnerEditor V E S P C'
  → DependentInnerEditor V E S P D'
dependent-inner-editor-map F e
  = record
  { DependentInnerEditor e
  ; pure-encoding
    = dependent-encoding-map F
      (DependentInnerEditor.pure-encoding e)
  ; split-functor
    = dependent-split-functor-compose F
      (DependentInnerEditor.split-functor e)
  }

-- ### DependentSimplePartialEditor

dependent-simple-partial-editor-map
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' D' : DependentSet C}
  → DependentPartialFunction C' D'
  → DependentSimplePartialEditor V E C'
  → DependentSimplePartialEditor V E D'
dependent-simple-partial-editor-map F e
  = record
  { DependentSimplePartialEditor e
  ; partial-function
    = dependent-simple-partial-function-compose F
      (DependentSimplePartialEditor.partial-function e)
  }

-- ### DependentSimpleSplitEditor

dependent-simple-split-editor-map
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C' D'
  → DependentSimpleSplitEditor V E C'
  → DependentSimpleSplitEditor V E D'
dependent-simple-split-editor-map F e
  = record
  { DependentSimpleSplitEditor e
  ; split-functor
    = dependent-simple-split-functor-compose F
      (DependentSimpleSplitEditor.split-functor e)
  }

-- ### DependentSimpleInnerEditor

dependent-simple-inner-editor-map
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C' D'
  → DependentSimpleInnerEditor V E S P C'
  → DependentSimpleInnerEditor V E S P D'
dependent-simple-inner-editor-map F e
  = record
  { DependentSimpleInnerEditor e
  ; pure-encoding
    = dependent-simple-encoding-map F
      (DependentSimpleInnerEditor.pure-encoding e)
  ; split-functor
    = dependent-simple-split-functor-compose F
      (DependentSimpleInnerEditor.split-functor e)
  }

-- ## Editors (nondependent)

-- ### SplitEditor

split-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {C D : Category}
  → SplitFunctor C D
  → SplitEditor V E C
  → SplitEditor V E D
split-editor-map
  = dependent-split-editor-map

-- ### InnerEditor

inner-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C D : Category}
  → SplitFunctor C D
  → InnerEditor V E S P C
  → InnerEditor V E S P D
inner-editor-map
  = dependent-inner-editor-map

-- ### SimplePartialEditor

simple-partial-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {A B : Set}
  → PartialFunction A B
  → SimplePartialEditor V E A
  → SimplePartialEditor V E B
simple-partial-editor-map
  = dependent-simple-partial-editor-map

-- ### SimpleSplitEditor

simple-split-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {A B : Set}
  → SplitFunction A B
  → SimpleSplitEditor V E A
  → SimpleSplitEditor V E B
simple-split-editor-map
  = dependent-simple-split-editor-map

-- ### SimpleInnerEditor

simple-inner-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {S P A B : Set}
  → SplitFunction A B
  → SimpleInnerEditor V E S P A
  → SimpleInnerEditor V E S P B
simple-inner-editor-map
  = dependent-simple-inner-editor-map

