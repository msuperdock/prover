module Prover.Editor.Simple.Formula where

open import Editor.Flat
  using (FlatEditor)
open import Editor.Flat.Map
  using (flat-editor-map)
open import Editor.Simple
  using (SimpleEditor; SimplePartialEditor; SimpleSplitEditor)
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

open import Prover.Data.Any
  using (Any)
open import Prover.Data.Bool
  using (Bool)
open import Prover.Data.Direction
  using (Direction)
open import Prover.Data.Equal
  using (_≡_; refl)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Formula.State
  using (SandboxState; SandboxStatePath; end)
open import Prover.Data.Formula.Insert
  using (sandbox-state-insert-parens; sandbox-state-insert-symbol;
    sandbox-state-insert-variable)
open import Prover.Data.Function
  using (_$_; id)
open import Prover.Data.Maybe
  using (Maybe; nothing)
open import Prover.Data.Sigma
  using (Σ; _,_)
open import Prover.Data.Sum
  using (ι₁; ι₂)
open import Prover.Data.Symbol
  using (symbol)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Unit
  using (tt)
open import Prover.Data.Variable
  using (variable')
open import Prover.Data.Variables
  using (Variables)
open import Prover.Draw.Formula
  using (draw-path-sandbox; draw-sandbox)
open import Prover.Editor.Flat.Command
  using (flat-editor-command)
open import Prover.Event.Formula
  using (FormulaEvent)
open import Prover.Stack.Flat.Command
  using (flat-view-stack-command)
open import Prover.Stack.Formula
  using (event-stack-formula; view-stack-formula)
open import Prover.View.Formula
  using (FormulaView; FormulaViewPath)

-- ## SimpleBaseEditor

-- ### View

base-view-stack-formula
  : BaseViewStack
base-view-stack-formula
  = record
  { View
    = FormulaView
  ; ViewPath
    = FormulaViewPath
  }

-- ### Event

data FormulaBaseEvent
  : Set
  where

  insert-parens
    : FormulaBaseEvent

base-event-stack-formula
  : BaseEventStack
base-event-stack-formula
  = record
  { Event
    = FormulaBaseEvent
  }

-- ### Module

module SimpleBaseEditorFormula
  (ss : Symbols)
  (vs : Variables)
  (m : Bool)
  where

  -- #### Types

  open BaseViewStack base-view-stack-formula
  open BaseEventStack base-event-stack-formula

  State
    : Set
  State
    = Any (SandboxState ss vs m)

  -- #### State

  StatePath
    : State
    → Set
  StatePath
    = SandboxStatePath

  initial
    : State
  initial
    = SandboxState.hole

  initial-path
    : (s : State)
    → StatePath s
  initial-path _
    = end

  initial-path-with
    : (s : State)
    → Direction
    → StatePath s
  initial-path-with s Direction.up
    = SandboxStatePath.leftmost s
  initial-path-with s Direction.down
    = SandboxStatePath.leftmost s
  initial-path-with s Direction.left
    = SandboxStatePath.leftmost s
  initial-path-with _ Direction.right
    = end

  -- #### Draw

  draw
    : State
    → View
  draw s
    = draw-sandbox s

  draw-with
    : (s : State)
    → StatePath s
    → View
  draw-with s _
    = draw s

  draw-path
    : (s : State)
    → (sp : StatePath s)
    → ViewPath (draw-with s sp)
  draw-path
    = draw-path-sandbox

  -- #### Handle

  handle
    : (s : State)
    → StatePath s
    → Event
    → Σ State StatePath
  handle s sp insert-parens
    = sandbox-state-insert-parens s sp

  handle-direction
    : (s : State)
    → StatePath s
    → Direction
    → Maybe (StatePath s)
  handle-direction _ _ Direction.up
    = nothing
  handle-direction _ _ Direction.down
    = nothing
  handle-direction _ sp Direction.left
    = SandboxStatePath.left sp
  handle-direction _ sp Direction.right
    = SandboxStatePath.right sp

  handle-direction-valid
    : (s : State)
    → (d : Direction)
    → handle-direction s (initial-path-with s d) d ≡ nothing
  handle-direction-valid _ Direction.up
    = refl
  handle-direction-valid _ Direction.down
    = refl
  handle-direction-valid s Direction.left
    = SandboxStatePath.left-leftmost s
  handle-direction-valid _ Direction.right
    = refl

-- ### Editor

simple-base-editor-formula
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleBaseEditor
    base-view-stack-formula
    base-event-stack-formula
    (Any (SandboxState ss vs m))
simple-base-editor-formula ss vs m
  = record {SimpleBaseEditorFormula ss vs m}

-- ## SimpleChildEditor

-- ### Key

data FormulaKey
  : Set
  where

  variable'
    : FormulaKey

  symbol
    : FormulaKey

-- ### View

flat-view-stack-formula-child
  : FormulaKey
  → FlatViewStack
flat-view-stack-formula-child _
  = flat-view-stack-command

-- ### Event

flat-event-stack-formula-child
  : FormulaKey
  → FlatEventStack
flat-event-stack-formula-child _
  = flat-event-stack-text

-- ### Variable

module SimpleChildEditorFormulaVariable
  (ss : Symbols)
  (vs : Variables)
  (m : Bool)
  where

  BaseState
    : Set
  BaseState
    = Any (SandboxState ss vs m)

  open SimpleBaseEditor (simple-base-editor-formula ss vs m)
    using () renaming
    ( StatePath
      to BaseStatePath
    )

  Result
    : (s : BaseState)
    → BaseStatePath s
    → Set
  Result _ _
    = Variables.Member vs

  flat-editor
    : (s : BaseState)
    → (sp : BaseStatePath s)
    → FlatEditor
      (flat-view-stack-formula-child variable')
      (flat-event-stack-formula-child variable')
      (Result s sp)
  flat-editor _ _
    = flat-editor-map (Variables.lookup-member vs)
    $ flat-editor-command "v"

  update
    : (s : BaseState)
    → (sp : BaseStatePath s)
    → Result s sp
    → Σ BaseState BaseStatePath
  update s sp (Variables.member v p)
    = sandbox-state-insert-variable s sp v p

simple-child-editor-formula-variable
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleChildEditor
    (flat-view-stack-formula-child variable')
    (flat-event-stack-formula-child variable')
    (simple-base-editor-formula ss vs m)
simple-child-editor-formula-variable ss vs m
  = record {SimpleChildEditorFormulaVariable ss vs m}

-- ### Symbol

module SimpleChildEditorFormulaSymbol
  (ss : Symbols)
  (vs : Variables)
  (m : Bool)
  where

  BaseState
    : Set
  BaseState
    = Any (SandboxState ss vs m)

  open SimpleBaseEditor (simple-base-editor-formula ss vs m)
    using () renaming
    ( StatePath
      to BaseStatePath
    )

  Result
    : (s : BaseState)
    → BaseStatePath s
    → Set
  Result _ _
    = Symbols.Member ss

  flat-editor
    : (s : BaseState)
    → (sp : BaseStatePath s)
    → FlatEditor
      (flat-view-stack-formula-child symbol)
      (flat-event-stack-formula-child symbol)
      (Result s sp)
  flat-editor _ _
    = flat-editor-map (Symbols.lookup-member ss)
    $ flat-editor-command "s"

  update
    : (s : BaseState)
    → (sp : BaseStatePath s)
    → Result s sp
    → Σ BaseState BaseStatePath
  update s sp (Symbols.member s' p)
    = sandbox-state-insert-symbol s sp s' p

simple-child-editor-formula-symbol
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleChildEditor
    (flat-view-stack-formula-child symbol)
    (flat-event-stack-formula-child symbol)
    (simple-base-editor-formula ss vs m)
simple-child-editor-formula-symbol ss vs m
  = record {SimpleChildEditorFormulaSymbol ss vs m}

-- ### Editor

formula-simple-child-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → (k : FormulaKey)
  → SimpleChildEditor
    (flat-view-stack-formula-child k)
    (flat-event-stack-formula-child k)
    (simple-base-editor-formula ss vs m)
formula-simple-child-editor ss vs m variable'
  = simple-child-editor-formula-variable ss vs m
formula-simple-child-editor ss vs m symbol
  = simple-child-editor-formula-symbol ss vs m

-- ## SimpleEditor

-- ### Parent

view-stack-formula-parent
  : ViewStack
view-stack-formula-parent
  = view-stack-parent
    base-view-stack-formula
    flat-view-stack-formula-child

event-stack-formula-parent
  : EventStack
event-stack-formula-parent
  = event-stack-parent
    base-event-stack-formula
    flat-event-stack-formula-child

simple-editor-formula-parent
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleEditor
    view-stack-formula-parent
    event-stack-formula-parent
    (Any (SandboxState ss vs m))
simple-editor-formula-parent ss vs m
  = simple-editor-parent
    flat-view-stack-formula-child
    flat-event-stack-formula-child
    (simple-base-editor-formula ss vs m)
    (formula-simple-child-editor ss vs m)

-- ### View

module ViewStackMapFormula where

  view
    : ViewStack.View view-stack-formula-parent
    → ViewStack.View view-stack-formula
  view
    = id

  view-with
    : (v : ViewStack.View view-stack-formula-parent)
    → ViewStack.ViewPath view-stack-formula-parent v
    → ViewStack.View view-stack-formula
  view-with v _
    = view v
  
  view-path
    : (v : ViewStack.View view-stack-formula-parent)
    → (vp : ViewStack.ViewPath view-stack-formula-parent v)
    → ViewStack.ViewPath view-stack-formula
      (view-with v vp)
  view-path _
    = id

  view-inner-with
    : (v : ViewStack.View view-stack-formula-parent)
    → (vp : ViewStack.ViewPath view-stack-formula-parent v)
    → (v' : ViewStack.ViewInner view-stack-formula-parent v vp)
    → ViewStack.ViewInnerPath view-stack-formula-parent v vp v'
    → ViewStack.ViewInner view-stack-formula
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ _ (_ , c) _
    = c

  view-inner-path
    : (v : ViewStack.View view-stack-formula-parent)
    → (vp : ViewStack.ViewPath view-stack-formula-parent v)
    → (v' : ViewStack.ViewInner view-stack-formula-parent v vp)
    → (vp' : ViewStack.ViewInnerPath view-stack-formula-parent v vp v')
    → ViewStack.ViewInnerPath view-stack-formula
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ _ _
    = id

view-stack-map-formula
  : ViewStackMap
    view-stack-formula-parent
    view-stack-formula
view-stack-map-formula
  = record {ViewStackMapFormula}

-- ### Event

module EventStackMapFormula where

  mode
    : EventStack.Mode event-stack-formula-parent
    → EventStack.Mode event-stack-formula
  mode
    = id

  mode-inner
    : EventStack.ModeInner event-stack-formula-parent
    → EventStack.ModeInner event-stack-formula
  mode-inner _
    = tt

  event
    : (m : EventStack.Mode event-stack-formula-parent)
    → EventStack.Event event-stack-formula (mode m)
    → EventStack.Event event-stack-formula-parent m
  event _ FormulaEvent.insert-parens
    = ι₁ insert-parens
  event _ FormulaEvent.insert-variable
    = ι₂ variable'
  event _ FormulaEvent.insert-symbol
    = ι₂ symbol

  event-inner
    : (m : EventStack.ModeInner event-stack-formula-parent)
    → EventStack.EventInner event-stack-formula (mode-inner m)
    → EventStack.EventInner event-stack-formula-parent m
  event-inner _
    = id

event-stack-map-formula
  : EventStackMap
    event-stack-formula-parent
    event-stack-formula
event-stack-map-formula
  = record {EventStackMapFormula}

-- ### Editor

simple-editor-formula
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleEditor
    view-stack-formula
    event-stack-formula
    (Any (SandboxState ss vs m))
simple-editor-formula ss vs m
  = simple-editor-map-view view-stack-map-formula
  $ simple-editor-map-event event-stack-map-formula
  $ simple-editor-formula-parent ss vs m

-- ## SimpleSplitEditor

simple-split-editor-formula
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleSplitEditor
    view-stack-formula
    event-stack-formula
    (Formula ss vs m)
simple-split-editor-formula ss vs m
  = record
  { editor
    = simple-editor-formula ss vs m
  ; split-functor
    = SandboxState.simple-split-functor ss vs m
  }

-- ## SimplePartialEditor

simple-partial-editor-formula
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimplePartialEditor
    view-stack-formula
    event-stack-formula
    (Formula ss vs m)
simple-partial-editor-formula ss vs m
  = SimpleSplitEditor.partial-editor (simple-split-editor-formula ss vs m)

