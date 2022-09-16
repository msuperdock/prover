module Prover.Editor.Simple.Proof.Meta where

open import Editor.Simple
  using (SimplePartialEditor)
open import Editor.Simple.Map.Event
  using (simple-partial-editor-map-event)
open import Editor.Simple.Map.View
  using (simple-partial-editor-map-view-with)
open import Editor.Simple.Product
  using (simple-partial-editor-product)
open import Stack
  using (EventStack; EventStackMap; ViewStack; ViewStackMap)
open import Stack.Nat
  using (event-stack-nat)
open import Stack.Product
  using (event-stack-product; view-stack-product)

open import Prover.Data.Bool
  using (Bool; false; true)
open import Prover.Data.Direction
  using (Direction)
open import Prover.Data.Fin
  using (zero; suc)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Function
  using (_$_; id)
open import Prover.Data.List
  using ([]; _∷_)
open import Prover.Data.Maybe
  using (just; nothing)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Sigma
  using (_×_; _,_)
open import Prover.Data.String
  using (String)
open import Prover.Data.Sum
  using (ι₁; ι₂)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Unit
  using (tt)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Editor.Simple.Formula
  using (simple-partial-editor-formula)
open import Prover.Editor.Simple.Meta
  using (simple-partial-editor-meta)
open import Prover.Event.Proof.Meta
  using (ProofMetaMode)
open import Prover.Stack.Formula
  using (event-stack-formula; view-stack-formula)
open import Prover.Stack.Proof.Meta
  using (event-stack-proof-meta)
open import Prover.Stack.RichText
  using (view-stack-rich-text)
open import Prover.Stack.Window
  using (view-stack-window)
open import Prover.View.Line
  using (Line)
open import Prover.View.RichText
  using (RichText; plain; text)
open import Prover.View.Window
  using (Window; go)

-- ## SimplePartialEditor

-- ### Product

view-stack-proof-meta-product
  : ViewStack
view-stack-proof-meta-product
  = view-stack-product
    view-stack-rich-text
    view-stack-formula

event-stack-proof-meta-product
  : EventStack
event-stack-proof-meta-product
  = event-stack-product
    event-stack-nat
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

-- ### View

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
    → ViewStack.View view-stack-window
  view (m , f)
    = view-window false m f

  view-with
    : (v : ViewStack.View view-stack-proof-meta-product)
    → ViewStack.ViewPath view-stack-proof-meta-product v
    → ViewStack.View view-stack-window
  view-with (m , f) (ι₁ _)
    = view-window false m f
  view-with (m , f) (ι₂ nothing)
    = view-window true m f
  view-with (m , f) (ι₂ (just _))
    = view-window false m f
  
  view-path
    : (v : ViewStack.View view-stack-proof-meta-product)
    → (vp : ViewStack.ViewPath view-stack-proof-meta-product v)
    → ViewStack.ViewPath view-stack-window
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
    → ViewStack.ViewInner view-stack-window
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ (ι₂ _) c _
    = c

  view-inner-path
    : (v : ViewStack.View view-stack-proof-meta-product)
    → (vp : ViewStack.ViewPath view-stack-proof-meta-product v)
    → (v' : ViewStack.ViewInner view-stack-proof-meta-product v vp)
    → (vp' : ViewStack.ViewInnerPath view-stack-proof-meta-product v vp v')
    → ViewStack.ViewInnerPath view-stack-window
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ (ι₂ _) _ cp
    = cp

view-stack-map-proof-meta
  : Bool
  → ViewStackMap
    view-stack-proof-meta-product
    view-stack-window
view-stack-map-proof-meta b
  = record {ViewStackMapProofMeta b}

-- ### Event

module EventStackMapProofMeta where

  mode
    : EventStack.Mode event-stack-proof-meta-product
    → EventStack.Mode event-stack-proof-meta
  mode (ι₁ _)
    = ProofMetaMode.nat
  mode (ι₂ _)
    = ProofMetaMode.formula

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

-- ### Editor

simple-partial-editor-proof-meta
  : (ss : Symbols)
  → (vs : Variables)
  → SimplePartialEditor
    view-stack-window
    event-stack-proof-meta
    (Meta × Formula ss vs false)
simple-partial-editor-proof-meta ss vs
  = simple-partial-editor-map-view-with view-stack-map-proof-meta
  $ simple-partial-editor-map-event event-stack-map-proof-meta
  $ simple-partial-editor-proof-meta-product ss vs

