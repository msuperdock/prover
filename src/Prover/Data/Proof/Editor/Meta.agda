module Prover.Data.Proof.Editor.Meta where

open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Formula.Editor
  using (FormulaEvent; FormulaEventStack; FormulaViewStack;
    formula-partial-editor)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Meta.Editor
  using (meta-partial-editor)
open import Prover.Data.Number.Editor
  using (NumberEvent; NumberEventStack)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text.Editor
  using (TextEvent)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Editor
  using (EventStack; EventStackMap; PartialEditor; ViewStack; ViewStackMap)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatEventStackMap)
open import Prover.Editor.Flatten
  using (event-stack-flatten; partial-editor-flatten)
open import Prover.Editor.Map
  using (flat-editor-map-event; partial-editor-map-event;
    partial-editor-map-view-with)
open import Prover.Editor.Product
  using (event-stack-product; partial-editor-product; view-stack-product)
open import Prover.View.Line
  using (Line)
open import Prover.View.Text
  using (RichText; RichTextViewStack; plain; text)
open import Prover.View.Window
  using (Window; WindowFlatViewStack; WindowViewStack; go)
open import Prover.Prelude

open Vec
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

ProofMetaEventStack
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

ProofMetaFlatEventStack
  : FlatEventStack
ProofMetaFlatEventStack
  = record
  { Mode
    = ProofMetaFlatMode
  ; Event
    = ProofMetaFlatEvent
  }

-- ## Editors

-- ### Product

-- #### View

ProofMetaProductViewStack
  : ViewStack
ProofMetaProductViewStack
  = view-stack-product
    RichTextViewStack
    FormulaViewStack

-- #### Event

ProofMetaProductEventStack
  : EventStack
ProofMetaProductEventStack
  = event-stack-product
    NumberEventStack
    FormulaEventStack

-- #### Editor

proof-meta-product-editor
  : (ss : Symbols)
  → (vs : Variables)
  → PartialEditor
    ProofMetaProductViewStack
    ProofMetaProductEventStack
    (Meta × Formula ss vs false)
proof-meta-product-editor ss vs
  = partial-editor-product
    Direction.right
    meta-partial-editor
    (formula-partial-editor ss vs false)

-- ### Partial

-- #### View

module ProofMetaViewStackMap
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
    : ViewStack.View ProofMetaProductViewStack
    → ViewStack.View WindowViewStack
  view (m , f)
    = view-window false m f

  view-with
    : (v : ViewStack.View ProofMetaProductViewStack)
    → ViewStack.ViewPath ProofMetaProductViewStack v
    → ViewStack.View WindowViewStack
  view-with (m , f) (ι₁ _)
    = view-window false m f
  view-with (m , f) (ι₂ nothing)
    = view-window true m f
  view-with (m , f) (ι₂ (just _))
    = view-window false m f
  
  view-path
    : (v : ViewStack.View ProofMetaProductViewStack)
    → (vp : ViewStack.ViewPath ProofMetaProductViewStack v)
    → ViewStack.ViewPath WindowViewStack
      (view-with v vp)
  view-path _ (ι₁ tp)
    = go zero (text zero tp)
  view-path _ (ι₂ nothing)
    = go zero (text (suc (suc (suc zero))) (plain (suc zero)))
  view-path _ (ι₂ (just fp))
    = go zero (text (suc (suc zero)) fp)

  view-inner-with
    : (v : ViewStack.View ProofMetaProductViewStack)
    → (vp : ViewStack.ViewPath ProofMetaProductViewStack v)
    → (v' : ViewStack.ViewInner ProofMetaProductViewStack v vp)
    → ViewStack.ViewInnerPath ProofMetaProductViewStack v vp v'
    → ViewStack.ViewInner WindowViewStack
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ (ι₂ _) c _
    = c

  view-inner-path
    : (v : ViewStack.View ProofMetaProductViewStack)
    → (vp : ViewStack.ViewPath ProofMetaProductViewStack v)
    → (v' : ViewStack.ViewInner ProofMetaProductViewStack v vp)
    → (vp' : ViewStack.ViewInnerPath ProofMetaProductViewStack v vp v')
    → ViewStack.ViewInnerPath WindowViewStack
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ (ι₂ _) _ cp
    = cp

proof-meta-view-stack-map
  : Bool
  → ViewStackMap
    ProofMetaProductViewStack
    WindowViewStack
proof-meta-view-stack-map b
  = record {ProofMetaViewStackMap b}

-- #### Event

module ProofMetaEventStackMap where

  mode
    : EventStack.Mode ProofMetaProductEventStack
    → EventStack.Mode ProofMetaEventStack
  mode (ι₁ _)
    = number
  mode (ι₂ _)
    = formula

  mode-inner
    : EventStack.ModeInner ProofMetaProductEventStack
    → EventStack.ModeInner ProofMetaEventStack
  mode-inner _
    = tt

  event
    : (m : EventStack.Mode ProofMetaProductEventStack)
    → EventStack.Event ProofMetaEventStack (mode m)
    → EventStack.Event ProofMetaProductEventStack m
  event (ι₁ _)
    = id
  event (ι₂ _)
    = id

  event-inner
    : (m : EventStack.ModeInner ProofMetaProductEventStack)
    → EventStack.EventInner ProofMetaEventStack (mode-inner m)
    → EventStack.EventInner ProofMetaProductEventStack m
  event-inner (ι₂ _)
    = id

proof-meta-event-stack-map
  : EventStackMap
    ProofMetaProductEventStack
    ProofMetaEventStack
proof-meta-event-stack-map
  = record {ProofMetaEventStackMap}

-- #### Editor

proof-meta-partial-editor
  : (ss : Symbols)
  → (vs : Variables)
  → PartialEditor
    WindowViewStack
    ProofMetaEventStack
    (Meta × Formula ss vs false)
proof-meta-partial-editor ss vs
  = partial-editor-map-view-with proof-meta-view-stack-map
  $ partial-editor-map-event proof-meta-event-stack-map
  $ proof-meta-product-editor ss vs

-- ### Flat

-- #### Event

module ProofMetaFlatEventStackMap where

  mode
    : FlatEventStack.Mode (event-stack-flatten ProofMetaEventStack)
    → FlatEventStack.Mode ProofMetaFlatEventStack
  mode (ι₁ number)
    = number
  mode (ι₁ formula)
    = formula
  mode (ι₂ _)
    = text

  event
    : (m : FlatEventStack.Mode (event-stack-flatten ProofMetaEventStack))
    → FlatEventStack.Event ProofMetaFlatEventStack (mode m)
    → FlatEventStack.Event (event-stack-flatten ProofMetaEventStack) m
  event (ι₁ number)
    = id
  event (ι₁ formula)
    = id
  event (ι₂ _)
    = id

proof-meta-flat-event-stack-map
  : FlatEventStackMap
    (event-stack-flatten ProofMetaEventStack)
    ProofMetaFlatEventStack
proof-meta-flat-event-stack-map
  = record {ProofMetaFlatEventStackMap}

-- #### Editor

proof-meta-flat-editor
  : (ss : Symbols)
  → (vs : Variables)
  → FlatEditor
    WindowFlatViewStack
    ProofMetaFlatEventStack
    (Meta × Formula ss vs false)
proof-meta-flat-editor ss vs
  = flat-editor-map-event proof-meta-flat-event-stack-map
  $ partial-editor-flatten
  $ proof-meta-partial-editor ss vs

