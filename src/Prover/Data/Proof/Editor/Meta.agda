module Prover.Data.Proof.Editor.Meta where

open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Formula.Editor
  using (FormulaEvent; event-stack-formula; simple-partial-editor-formula;
    view-stack-formula)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Meta.Editor
  using (simple-partial-editor-meta)
open import Prover.Data.Number.Editor
  using (NumberEvent; event-stack-number)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text.Editor
  using (TextEvent)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Editor
  using (EventStack; EventStackMap; SimplePartialEditor; ViewStack;
    ViewStackMap)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatEventStackMap)
open import Prover.Editor.Flatten
  using (event-stack-flatten; simple-partial-editor-flatten)
open import Prover.Editor.Map.Event
  using (flat-editor-map-event; simple-partial-editor-map-event)
open import Prover.Editor.Map.View
  using (simple-partial-editor-map-view-with)
open import Prover.Editor.Product
  using (event-stack-product; simple-partial-editor-product; view-stack-product)
open import Prover.View.Line
  using (Line)
open import Prover.View.Text
  using (RichText; RichTextViewStack; plain; text)
open import Prover.View.Window
  using (Window; WindowFlatViewStack; WindowViewStack; go)
open import Prover.Prelude

open List
  using ([]; _∷_)

-- ## Types

data ProofMetaMode
  : Set
  where

  number
    : ProofMetaMode

  formula
    : ProofMetaMode

data ProofMetaFlatMode
  : Set
  where

  text
    : ProofMetaFlatMode

  number
    : ProofMetaFlatMode

  formula
    : ProofMetaFlatMode

ProofMetaEvent
  : ProofMetaMode
  → Set
ProofMetaEvent number
  = NumberEvent
ProofMetaEvent formula
  = FormulaEvent

ProofMetaFlatEvent
  : ProofMetaFlatMode
  → Set
ProofMetaFlatEvent text
  = TextEvent
ProofMetaFlatEvent number
  = NumberEvent
ProofMetaFlatEvent formula
  = FormulaEvent

event-stack-proof-meta
  = record
  { Mode
    = ProofMetaMode
  ; ModeInner
    = ⊤
  ; Event
    = ProofMetaEvent
  ; EventInner
    = λ _ → TextEvent
  }

flat-event-stack-proof-meta
  : FlatEventStack
flat-event-stack-proof-meta
  = record
  { Mode
    = ProofMetaFlatMode
  ; Event
    = ProofMetaFlatEvent
  }

-- ## Editors

-- ### SimplePartialEditor

-- #### Product

view-stack-proof-meta-product
  : ViewStack
view-stack-proof-meta-product
  = view-stack-product
    RichTextViewStack
    view-stack-formula

event-stack-proof-meta-product
  : EventStack
event-stack-proof-meta-product
  = event-stack-product
    event-stack-number
    event-stack-formula

simple-partial-editor-proof-meta-product
  : (ss : Symbols)
  → (vs : Variables)
  → SimplePartialEditor
    view-stack-proof-meta-product
    event-stack-proof-meta-product
    (Meta × Formula ss vs false)
simple-partial-editor-proof-meta-product ss vs
  = simple-partial-editor-product Direction.right
    simple-partial-editor-meta
    (simple-partial-editor-formula ss vs false)

-- #### View

module ViewStackMapProofMeta
  (b : Bool)
  where

  view-string
    : Bool
    → String
  view-string false
    = ""
  view-string true
    = "  "

  view-line
    : Bool
    → RichText
    → RichText
    → Line
  view-line p m f
    = record
    { status
      = true
    ; text
      = RichText.texts
      $ m
      ∷ RichText.string " ↪ "
      ∷ f
      ∷ RichText.string (view-string p)
      ∷ []
    }

  view-window
    : Bool
    → RichText
    → RichText
    → Window
  view-window p m f
    = record
    { name
      = "meta-substitution"
    ; status
      = b
    ; lines
      = view-line p m f ∷ []
    }

  view
    : ViewStack.View view-stack-proof-meta-product
    → ViewStack.View WindowViewStack
  view (m , f)
    = view-window false m f

  view-with
    : (v : ViewStack.View view-stack-proof-meta-product)
    → ViewStack.ViewPath view-stack-proof-meta-product v
    → ViewStack.View WindowViewStack
  view-with (m , f) (ι₁ _)
    = view-window false m f
  view-with (m , f) (ι₂ nothing)
    = view-window true m f
  view-with (m , f) (ι₂ (just _))
    = view-window false m f
  
  view-path
    : (v : ViewStack.View view-stack-proof-meta-product)
    → (vp : ViewStack.ViewPath view-stack-proof-meta-product v)
    → ViewStack.ViewPath WindowViewStack
      (view-with v vp)
  view-path _ (ι₁ tp)
    = go zero (text zero tp)
  view-path _ (ι₂ nothing)
    = go zero (text (suc (suc (suc zero))) (plain (suc zero)))
  view-path _ (ι₂ (just fp))
    = go zero (text (suc (suc zero)) fp)

  view-inner-with
    : (v : ViewStack.View view-stack-proof-meta-product)
    → (vp : ViewStack.ViewPath view-stack-proof-meta-product v)
    → (v' : ViewStack.ViewInner view-stack-proof-meta-product v vp)
    → ViewStack.ViewInnerPath view-stack-proof-meta-product v vp v'
    → ViewStack.ViewInner WindowViewStack
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ (ι₂ _) c _
    = c

  view-inner-path
    : (v : ViewStack.View view-stack-proof-meta-product)
    → (vp : ViewStack.ViewPath view-stack-proof-meta-product v)
    → (v' : ViewStack.ViewInner view-stack-proof-meta-product v vp)
    → (vp' : ViewStack.ViewInnerPath view-stack-proof-meta-product v vp v')
    → ViewStack.ViewInnerPath WindowViewStack
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ (ι₂ _) _ cp
    = cp

view-stack-map-proof-meta
  : Bool
  → ViewStackMap
    view-stack-proof-meta-product
    WindowViewStack
view-stack-map-proof-meta b
  = record {ViewStackMapProofMeta b}

-- #### Event

module EventStackMapProofMeta where

  mode
    : EventStack.Mode event-stack-proof-meta-product
    → EventStack.Mode event-stack-proof-meta
  mode (ι₁ _)
    = number
  mode (ι₂ _)
    = formula

  mode-inner
    : EventStack.ModeInner event-stack-proof-meta-product
    → EventStack.ModeInner event-stack-proof-meta
  mode-inner _
    = tt

  event
    : (m : EventStack.Mode event-stack-proof-meta-product)
    → EventStack.Event event-stack-proof-meta (mode m)
    → EventStack.Event event-stack-proof-meta-product m
  event (ι₁ _)
    = id
  event (ι₂ _)
    = id

  event-inner
    : (m : EventStack.ModeInner event-stack-proof-meta-product)
    → EventStack.EventInner event-stack-proof-meta (mode-inner m)
    → EventStack.EventInner event-stack-proof-meta-product m
  event-inner (ι₂ _)
    = id

event-stack-map-proof-meta
  : EventStackMap
    event-stack-proof-meta-product
    event-stack-proof-meta
event-stack-map-proof-meta
  = record {EventStackMapProofMeta}

-- #### Editor

simple-partial-editor-proof-meta
  : (ss : Symbols)
  → (vs : Variables)
  → SimplePartialEditor
    WindowViewStack
    event-stack-proof-meta
    (Meta × Formula ss vs false)
simple-partial-editor-proof-meta ss vs
  = simple-partial-editor-map-view-with view-stack-map-proof-meta
  $ simple-partial-editor-map-event event-stack-map-proof-meta
  $ simple-partial-editor-proof-meta-product ss vs

-- ### FlatEditor

-- #### Event

module FlatEventStackMapProofMeta where

  mode
    : FlatEventStack.Mode (event-stack-flatten event-stack-proof-meta)
    → FlatEventStack.Mode flat-event-stack-proof-meta
  mode (ι₁ number)
    = number
  mode (ι₁ formula)
    = formula
  mode (ι₂ _)
    = text

  event
    : (m : FlatEventStack.Mode (event-stack-flatten event-stack-proof-meta))
    → FlatEventStack.Event flat-event-stack-proof-meta (mode m)
    → FlatEventStack.Event (event-stack-flatten event-stack-proof-meta) m
  event (ι₁ number)
    = id
  event (ι₁ formula)
    = id
  event (ι₂ _)
    = id

flat-event-stack-map-proof-meta
  : FlatEventStackMap
    (event-stack-flatten event-stack-proof-meta)
    flat-event-stack-proof-meta
flat-event-stack-map-proof-meta
  = record {FlatEventStackMapProofMeta}

-- #### Editor

flat-editor-proof-meta
  : (ss : Symbols)
  → (vs : Variables)
  → FlatEditor
    WindowFlatViewStack
    flat-event-stack-proof-meta
    (Meta × Formula ss vs false)
flat-editor-proof-meta ss vs
  = flat-editor-map-event flat-event-stack-map-proof-meta
  $ simple-partial-editor-flatten
  $ simple-partial-editor-proof-meta ss vs

