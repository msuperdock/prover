module Prover.Data.Text.Editor where

open import Prover.Client.Aeson
  using (Value)
open import Prover.Data.Text
  using (Text; TextWith)
open import Prover.Editor
  using (EventStack; EventStackMap; SimpleEditor; SimpleSplitEditor)
open import Prover.Editor.Base
  using (BaseEventStack; BaseEventStackMap; BaseViewStack; SimpleBaseEditor)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatViewStack; FlatViewStackMap)
open import Prover.Editor.Flatten
  using (base-event-stack-flatten; base-event-stack-flatten-lift;
    base-view-stack-flatten-lift; simple-split-editor-flatten)
open import Prover.Editor.Lift
  using (event-stack-lift; event-stack-map-lift; simple-editor-lift)
open import Prover.Editor.Map
  using (simple-split-editor-map)
open import Prover.Editor.Map.Event
  using (flat-editor-map-event; simple-split-editor-map-event)
open import Prover.Editor.Map.View
  using (flat-editor-map-view)
open import Prover.Function
  using (Function)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Split
  using (SplitFunction; retraction-split)
open import Prover.View.Command
  using (CommandFlatViewStack; command)
open import Prover.View.Text
  using (PlainTextBaseViewStack; PlainTextFlatViewStack; PlainTextViewStack)
open import Prover.Prelude

open List
  using ([]; _∷_)

-- ## Types

-- ### Event

data TextWithEvent
  (p : Char → Bool)
  : Set
  where

  delete-previous
    : TextWithEvent p

  delete-next
    : TextWithEvent p

  insert
    : CharWith p
    → TextWithEvent p

data TextEvent
  : Set
  where

  delete-previous
    : TextEvent

  delete-next
    : TextEvent

  insert
    : Char
    → TextEvent

base-event-stack-text-with
  : (Char → Bool)
  → BaseEventStack
base-event-stack-text-with p
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → TextWithEvent p
  }

base-event-stack-text
  : BaseEventStack
base-event-stack-text
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → TextEvent
  }

event-stack-text-with
  : (Char → Bool)
  → EventStack
event-stack-text-with p
  = event-stack-lift
    (base-event-stack-text-with p)

event-stack-text
  : EventStack
event-stack-text
  = event-stack-lift
    base-event-stack-text

flat-event-stack-text
  : FlatEventStack
flat-event-stack-text
  = base-event-stack-flatten
    base-event-stack-text

-- ### State

TextWithState
  : (Char → Bool)
  → Set
TextWithState p
  = List (CharWith p)

-- ## Encoding

-- ### Encode

encode-text
  : Text
  → Value
encode-text (c ∷ cs)
  = Value.string (List.to-builtin (c ∷ cs))

-- ### Decode

decode-text
  : Value
  → Maybe Text
decode-text (Value.string (cons c cs))
  = just (c ∷ List.from-builtin cs)
decode-text _
  = nothing

-- ### Valid

decode-encode-text
  : (t : Text)
  → decode-text (encode-text t) ≡ just t
decode-encode-text (c ∷ cs)
  = sub (λ x → just (c ∷ x)) (List.from-to-builtin cs)

-- ## Editors

-- ### SimpleBaseEditor

-- #### Module

module SimpleBaseEditorTextWith
  (p : Char → Bool)
  where

  -- ##### Types

  open BaseViewStack PlainTextBaseViewStack
  open BaseEventStack (base-event-stack-text-with p)

  State
    : Set
  State
    = List (CharWith p)

  -- ##### State

  StatePath
    : State
    → Set
  StatePath cs
    = Fin (suc (List.length cs))

  initial
    : State
  initial
    = []

  initial-path
    : (s : State)
    → StatePath s
  initial-path cs
    = Fin.maximum (List.length cs)

  initial-path-with
    : (s : State)
    → Direction
    → StatePath s
  initial-path-with _ Direction.up
    = zero
  initial-path-with _ Direction.down
    = zero
  initial-path-with _ Direction.left
    = zero
  initial-path-with cs Direction.right
    = Fin.maximum (List.length cs)

  -- ##### Draw

  draw
    : State
    → View
  draw
    = List.map CharWith.char

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
  draw-path _
    = Fin.drop

  -- ##### Mode

  mode
    : (s : State)
    → StatePath s
    → Mode
  mode _ _
    = tt

  -- ##### Handle

  handle
    : (s : State)
    → (sp : StatePath s)
    → Event (mode s sp)
    → Σ State StatePath
  handle cs zero delete-previous
    = (cs , zero)
  handle cs@(_ ∷ _) (suc k) delete-previous
    = (List.delete cs k , k)
  handle [] _ delete-next
    = ([] , zero)
  handle (_ ∷ cs) zero delete-next
    = (cs , zero)
  handle (c ∷ cs) (suc k) delete-next
    with handle cs k delete-next
  ... | (cs' , k')
    = (c ∷ cs' , suc k')
  handle cs k (insert c)
    = (List.insert cs k c , suc k)

  handle-direction
    : (s : State)
    → StatePath s
    → Direction
    → Maybe (StatePath s)
  handle-direction _ _ Direction.up
    = nothing
  handle-direction _ _ Direction.down
    = nothing
  handle-direction _ k Direction.left
    = Fin.decrement k
  handle-direction _ k Direction.right
    = Fin.increment k

  handle-direction-valid
    : (s : State)
    → (d : Direction)
    → handle-direction s (initial-path-with s d) d ≡ nothing
  handle-direction-valid _ Direction.up
    = refl
  handle-direction-valid _ Direction.down
    = refl
  handle-direction-valid _ Direction.left
    = refl
  handle-direction-valid cs Direction.right
    = Fin.increment-maximum (List.length cs)

-- #### Function

simple-base-editor-text-with
  : (p : Char → Bool)
  → SimpleBaseEditor
    PlainTextBaseViewStack
    (base-event-stack-text-with p)
    (TextWithState p)
simple-base-editor-text-with p
  = record {SimpleBaseEditorTextWith p}

-- ### SimpleEditor

simple-editor-text-with
  : (p : Char → Bool)
  → SimpleEditor
    PlainTextViewStack
    (event-stack-text-with p)
    (TextWithState p)
simple-editor-text-with p
  = simple-editor-lift
    (simple-base-editor-text-with p)

-- ### SimpleSplitEditor

-- #### TextWith

module SplitFunctionTextWith
  (p : Char → Bool)
  where

  base
    : TextWithState p
    → Maybe (TextWith p)
  base []
    = nothing
  base (c ∷ cs)
    = just (c ∷ cs)

  partial-function
    : PartialFunction
      (TextWithState p)
      (TextWith p)
  partial-function
    = record
    { base
      = base
    }

  unbase
    : TextWith p
    → TextWithState p
  unbase (c ∷ cs)
    = c ∷ cs

  function
    : Function
      (TextWith p)
      (TextWithState p)
  function
    = record
    { base
      = unbase
    }

  base-unbase
    : (t : TextWith p)
    → base (unbase t) ≡ just t
  base-unbase (_ ∷ _)
    = refl

split-function-text-with
  : (p : Char → Bool)
  → SplitFunction
    (TextWithState p)
    (TextWith p)
split-function-text-with p
  = record {SplitFunctionTextWith p}

simple-split-editor-text-with
  : (p : Char → Bool)
  → SimpleSplitEditor
    PlainTextViewStack
    (event-stack-text-with p)
    (TextWith p)
simple-split-editor-text-with p
  = record
  { editor
    = simple-editor-text-with p
  ; split-functor
    = split-function-text-with p
  }

-- #### Text

module BaseEventStackMapText where

  mode
    : BaseEventStack.Mode (base-event-stack-text-with (const true))
    → BaseEventStack.Mode base-event-stack-text
  mode
    = id

  event
    : (m : BaseEventStack.Mode (base-event-stack-text-with (const true)))
    → BaseEventStack.Event base-event-stack-text (mode m)
    → BaseEventStack.Event (base-event-stack-text-with (const true)) m
  event _ delete-previous
    = delete-previous
  event _ delete-next
    = delete-next
  event _ (insert c)
    = insert (char-with c refl)

base-event-stack-map-text
  : BaseEventStackMap
    (base-event-stack-text-with (const true))
    base-event-stack-text
base-event-stack-map-text
  = record {BaseEventStackMapText}

event-stack-map-text
  : EventStackMap
    (event-stack-text-with (const true))
    event-stack-text
event-stack-map-text
  = event-stack-map-lift
    base-event-stack-map-text

simple-split-editor-text
  : SimpleSplitEditor
    PlainTextViewStack
    event-stack-text
    Text
simple-split-editor-text
  = simple-split-editor-map-event event-stack-map-text
  $ simple-split-editor-map (retraction-split Text.retraction)
  $ simple-split-editor-text-with (const true)

-- ### FlatEditor

flat-editor-text
  : FlatEditor
    PlainTextFlatViewStack
    flat-event-stack-text
    Text
flat-editor-text
  = flat-editor-map-view (base-view-stack-flatten-lift PlainTextBaseViewStack)
  $ flat-editor-map-event (base-event-stack-flatten-lift base-event-stack-text)
  $ simple-split-editor-flatten
  $ simple-split-editor-text

-- ## Command

module FlatViewStackMapCommand
  (p : String)
  where

  view-with
    : (v : FlatViewStack.View PlainTextFlatViewStack)
    → FlatViewStack.ViewPath PlainTextFlatViewStack v
    → FlatViewStack.View CommandFlatViewStack
  view-with cs nothing
    = command p (List.snoc cs ' ')
  view-with t (just _)
    = command p t

  view-path
    : (v : FlatViewStack.View PlainTextFlatViewStack)
    → (vp : FlatViewStack.ViewPath PlainTextFlatViewStack v)
    → FlatViewStack.ViewPath CommandFlatViewStack (view-with v vp)
  view-path cs nothing
    = Fin.maximum (List.length cs)
  view-path _ (just k)
    = k

-- Takes a prompt string, not including colon or space.
flat-view-stack-map-command
  : String
  → FlatViewStackMap
    PlainTextFlatViewStack
    CommandFlatViewStack
flat-view-stack-map-command p
  = record {FlatViewStackMapCommand p}

-- Takes a prompt string, not including colon or space.
flat-editor-command
  : String
  → FlatEditor
    CommandFlatViewStack
    flat-event-stack-text
    Text
flat-editor-command s
  = flat-editor-map-view (flat-view-stack-map-command s)
  $ flat-editor-text

