module Prover.Editor.Simple.Proof where

open import Client.Aeson
  using (Value)
open import Editor.Flat
  using (FlatEditor)
open import Editor.Flat.Map
  using (flat-editor-map)
open import Editor.Simple
  using (SimpleEditor; SimpleMainEditor)
open import Editor.Simple.Base
  using (SimpleBaseEditor)
open import Editor.Simple.Child
  using (SimpleChildEditor)
open import Editor.Simple.Map.Event
  using (simple-editor-map-event)
open import Editor.Simple.Map.View
  using (simple-editor-map-view)
open import Editor.Simple.Parent
  using (simple-editor-parent)
open import Stack
  using (EventStack; EventStackMap; ViewStack; ViewStackMap)
open import Stack.Base
  using (BaseEventStack; BaseViewStack)
open import Stack.Flat
  using (FlatEventStack; FlatViewStack)
open import Stack.Flat.Text
  using (flat-event-stack-text)
open import Stack.Parent
  using (event-stack-parent; view-stack-parent)

open import Prover.Data.Bool
  using (false)
open import Prover.Data.Direction
  using (Direction)
open import Prover.Data.Empty
  using (⊥)
open import Prover.Data.Equal
  using (_≡_; refl)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Function
  using (_$_; id)
open import Prover.Data.List
  using (List)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Proof
  using (Proof; ProofPath; stop)
open import Prover.Data.Relation
  using (no; yes)
open import Prover.Data.Rule
  using (Rule)
open import Prover.Data.Rules
  using (Rules; rul_∈_)
open import Prover.Data.Sigma
  using (Σ; _×_; _,_)
open import Prover.Data.Sum
  using (ι₂)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text
  using (Text)
open import Prover.Data.Unit
  using (⊤)
open import Prover.Draw.Proof
  using (draw-proof; draw-proof-with)
open import Prover.Editor.Flat.Command
  using (flat-editor-command)
open import Prover.Editor.Flat.Proof.Meta
  using (flat-editor-proof-meta)
open import Prover.Encoding.Proof
  using (encoding-proof)
open import Prover.Event.Proof
  using (ProofEvent; ProofModeInner)
open import Prover.Event.Flat.Proof.Meta
  using (FlatProofMetaMode)
open import Prover.Stack.Flat.Command
  using (flat-view-stack-command)
open import Prover.Stack.Flat.Proof.Meta
  using (flat-event-stack-proof-meta)
open import Prover.Stack.Flat.Window
  using (flat-view-stack-window)
open import Prover.Stack.Proof
  using (event-stack-proof; view-stack-proof)
open import Prover.View.Line
  using (Line)
open import Prover.View.Proof
  using (ProofViewInner; ProofViewInnerPath)

-- ## SimpleBaseEditor

-- ### View

base-view-stack-proof
  : BaseViewStack
base-view-stack-proof
  = record
  { View
    = List Line
  ; ViewPath
    = λ _ → ⊤
  }

-- ### Event

base-event-stack-proof
  : BaseEventStack
base-event-stack-proof
  = record
  { Event
    = ⊥
  }

-- ### Module

module SimpleBaseEditorProof
  {ss : Symbols}
  (rs : Rules ss)
  (r : Rule ss)
  where

  -- #### Types

  open BaseViewStack base-view-stack-proof
  open BaseEventStack base-event-stack-proof

  State
    : Set
  State
    = Proof rs r

  -- #### State

  StatePath
    : State
    → Set
  StatePath
    = ProofPath

  initial
    : State
  initial
    = Proof.assumption

  initial-path
    : (s : State)
    → StatePath s
  initial-path _
    = stop

  initial-path-with
    : (s : State)
    → Direction
    → StatePath s
  initial-path-with p Direction.up
    = ProofPath.top p
  initial-path-with _ Direction.down
    = stop
  initial-path-with _ Direction.left
    = stop
  initial-path-with _ Direction.right
    = stop

  -- #### Draw

  draw
    : State
    → View
  draw
    = draw-proof

  draw-with
    : (s : State)
    → StatePath s
    → View
  draw-with
    = draw-proof-with

  -- #### Handle

  handle
    : (s : State)
    → StatePath s
    → Event
    → Σ State StatePath
  handle _ _ ()

  handle-direction
    : (s : State)
    → StatePath s
    → Direction
    → Maybe (StatePath s)
  handle-direction p pp Direction.up
    = ProofPath.up p pp
  handle-direction p pp Direction.down
    = ProofPath.down p pp
  handle-direction _ _ Direction.left
    = nothing
  handle-direction _ _ Direction.right
    = nothing

  handle-direction-valid
    : (s : State)
    → (d : Direction)
    → handle-direction s (initial-path-with s d) d ≡ nothing
  handle-direction-valid p Direction.up
    = ProofPath.up-top p
  handle-direction-valid _ Direction.down
    = refl
  handle-direction-valid _ Direction.left
    = refl
  handle-direction-valid _ Direction.right
    = refl

-- ### Editor

simple-base-editor-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SimpleBaseEditor
    base-view-stack-proof
    base-event-stack-proof
    (Proof rs r)
simple-base-editor-proof rs r
  = record {SimpleBaseEditorProof rs r}

-- ## SimpleChildEditor

-- ### Key

data ProofKey
  : Set
  where

  infer
    : ProofKey

  meta
    : ProofKey

-- ### View

flat-view-stack-proof-child
  : ProofKey
  → FlatViewStack
flat-view-stack-proof-child infer
  = flat-view-stack-command
flat-view-stack-proof-child meta
  = flat-view-stack-window

-- ### Event

flat-event-stack-proof-child
  : ProofKey
  → FlatEventStack
flat-event-stack-proof-child infer
  = flat-event-stack-text
flat-event-stack-proof-child meta
  = flat-event-stack-proof-meta

-- ### Infer

module _
  {ss : Symbols}
  where

  module SimpleChildEditorProofInfer
    (rs : Rules ss)
    (r : Rule ss)
    where
  
    BaseState
      : Set
    BaseState
      = Proof rs r

    open SimpleBaseEditor (simple-base-editor-proof rs r)
      using () renaming
      ( StatePath
        to BaseStatePath
      )

    record Result
      (p : Proof rs r)
      (pp : ProofPath p)
      : Set
      where
  
      constructor
      
        result
  
      field
  
        value
          : Rule ss
  
        .member
          : rul value ∈ rs
  
        match
          : Formula.Match (Rule.conclusion value) (Proof.lookup p pp)

    result-map
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Text
      → Maybe (Result s sp)
    result-map p pp n
      with Rules.lookup-member rs n
    ... | nothing
      = nothing
    ... | just (Rules.member r q)
      with Formula.match? (Rule.conclusion r) (Proof.lookup p pp)
    ... | no _
      = nothing
    ... | yes m
      = just (result r q m)

    flat-editor
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → FlatEditor
        (flat-view-stack-proof-child infer)
        (flat-event-stack-proof-child infer)
        (Result s sp)
    flat-editor s sp
      = flat-editor-map (result-map s sp)
      $ flat-editor-command "i"

    update
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Result s sp
      → Σ BaseState BaseStatePath
    update p pp (result r q m)
      = Proof.infer p pp r q m

  simple-child-editor-proof-infer
    : (rs : Rules ss)
    → (r : Rule ss)
    → SimpleChildEditor
      (flat-view-stack-proof-child infer)
      (flat-event-stack-proof-child infer)
      (simple-base-editor-proof rs r)
  simple-child-editor-proof-infer rs r
    = record {SimpleChildEditorProofInfer rs r}

-- ### Meta

module _
  {ss : Symbols}
  where

  module SimpleChildEditorProofMeta
    (rs : Rules ss)
    (r : Rule ss)
    where

    BaseState
      : Set
    BaseState
      = Proof rs r

    open SimpleBaseEditor (simple-base-editor-proof rs r)
      using () renaming
      ( StatePath
        to BaseStatePath
      )

    Result
      : (s : BaseState)
      → BaseStatePath s
      → Set
    Result _ _
      = Meta × Formula ss (Rule.variables r) false

    flat-editor
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → FlatEditor
        (flat-view-stack-proof-child meta)
        (flat-event-stack-proof-child meta)
        (Result s sp)
    flat-editor _ _
      = flat-editor-proof-meta ss (Rule.variables r)

    update
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Result s sp
      → Σ BaseState BaseStatePath
    update p pp (m , f)
      = Proof.substitute-meta p pp m f

  simple-child-editor-proof-meta
    : (rs : Rules ss)
    → (r : Rule ss)
    → SimpleChildEditor
      (flat-view-stack-proof-child meta)
      (flat-event-stack-proof-child meta)
      (simple-base-editor-proof rs r)
  simple-child-editor-proof-meta rs r
    = record {SimpleChildEditorProofMeta rs r}

-- ### Editor

simple-child-editor-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → (k : ProofKey)
  → SimpleChildEditor
    (flat-view-stack-proof-child k)
    (flat-event-stack-proof-child k)
    (simple-base-editor-proof rs r)
simple-child-editor-proof rs r infer
  = simple-child-editor-proof-infer rs r
simple-child-editor-proof rs r meta
  = simple-child-editor-proof-meta rs r

-- ## SimpleEditor

-- ### Parent

view-stack-proof-parent
  : ViewStack
view-stack-proof-parent
  = view-stack-parent
    base-view-stack-proof
    flat-view-stack-proof-child

event-stack-proof-parent
  : EventStack
event-stack-proof-parent
  = event-stack-parent
    base-event-stack-proof
    flat-event-stack-proof-child

simple-editor-proof-parent
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SimpleEditor
    view-stack-proof-parent
    event-stack-proof-parent
    (Proof rs r)
simple-editor-proof-parent rs r
  = simple-editor-parent
    flat-view-stack-proof-child
    flat-event-stack-proof-child
    (simple-base-editor-proof rs r)
    (simple-child-editor-proof rs r)

-- ### View

module ViewStackMapProof where

  view
    : ViewStack.View view-stack-proof-parent
    → ViewStack.View view-stack-proof
  view
    = id

  view-with
    : (v : ViewStack.View view-stack-proof-parent)
    → ViewStack.ViewPath view-stack-proof-parent v
    → ViewStack.View view-stack-proof
  view-with v _
    = view v
  
  view-path
    : (v : ViewStack.View view-stack-proof-parent)
    → (vp : ViewStack.ViewPath view-stack-proof-parent v)
    → ViewStack.ViewPath view-stack-proof
      (view-with v vp)
  view-path _
    = id

  view-inner-with
    : (v : ViewStack.View view-stack-proof-parent)
    → (vp : ViewStack.ViewPath view-stack-proof-parent v)
    → (v' : ViewStack.ViewInner view-stack-proof-parent v vp)
    → ViewStack.ViewInnerPath view-stack-proof-parent v vp v'
    → ViewStack.ViewInner view-stack-proof
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ _ (infer , c) _
    = ProofViewInner.command c
  view-inner-with _ _ (meta , (w , nothing)) _
    = ProofViewInner.window w
  view-inner-with _ _ (meta , (w , just (_ , c))) _
    = ProofViewInner.both w c

  view-inner-path
    : (v : ViewStack.View view-stack-proof-parent)
    → (vp : ViewStack.ViewPath view-stack-proof-parent v)
    → (v' : ViewStack.ViewInner view-stack-proof-parent v vp)
    → (vp' : ViewStack.ViewInnerPath view-stack-proof-parent v vp v')
    → ViewStack.ViewInnerPath view-stack-proof
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ _ (infer , _) cp
    = ProofViewInnerPath.command cp
  view-inner-path _ _ (meta , (_ , nothing)) wp
    = ProofViewInnerPath.window wp
  view-inner-path _ _ (meta , (_ , just _)) cp
    = ProofViewInnerPath.both cp

view-stack-map-proof
  : ViewStackMap
    view-stack-proof-parent
    view-stack-proof
view-stack-map-proof
  = record {ViewStackMapProof}

-- ### Event

module EventStackMapProof where

  mode
    : EventStack.Mode event-stack-proof-parent
    → EventStack.Mode event-stack-proof
  mode
    = id

  mode-inner
    : EventStack.ModeInner event-stack-proof-parent
    → EventStack.ModeInner event-stack-proof
  mode-inner (infer , _)
    = ProofModeInner.text
  mode-inner (meta , FlatProofMetaMode.text)
    = ProofModeInner.text
  mode-inner (meta , FlatProofMetaMode.nat)
    = ProofModeInner.nat
  mode-inner (meta , FlatProofMetaMode.formula)
    = ProofModeInner.formula

  event
    : (m : EventStack.Mode event-stack-proof-parent)
    → EventStack.Event event-stack-proof (mode m)
    → EventStack.Event event-stack-proof-parent m
  event _ ProofEvent.infer-hypotheses
    = ι₂ infer
  event _ ProofEvent.substitute-meta
    = ι₂ meta

  event-inner
    : (m : EventStack.ModeInner event-stack-proof-parent)
    → EventStack.EventInner event-stack-proof (mode-inner m)
    → EventStack.EventInner event-stack-proof-parent m
  event-inner (infer , _)
    = id
  event-inner (meta , FlatProofMetaMode.text)
    = id
  event-inner (meta , FlatProofMetaMode.nat)
    = id
  event-inner (meta , FlatProofMetaMode.formula)
    = id

event-stack-map-proof
  : EventStackMap
    event-stack-proof-parent
    event-stack-proof
event-stack-map-proof
  = record {EventStackMapProof}

-- ### Editor

simple-editor-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SimpleEditor
    view-stack-proof
    event-stack-proof
    (Proof rs r)
simple-editor-proof rs r
  = simple-editor-map-view view-stack-map-proof
  $ simple-editor-map-event event-stack-map-proof
  $ simple-editor-proof-parent rs r

-- ## SimpleMainEditor

simple-main-editor-proof
  : {ss : Symbols}
  → Rules ss
  → Rule ss
  → SimpleMainEditor
    view-stack-proof
    event-stack-proof
    Value
simple-main-editor-proof rs r
  = record
  { editor
    = simple-editor-proof rs r
  ; state-encoding
    = encoding-proof rs r
  ; bool-function
    = Proof.is-complete
  }

