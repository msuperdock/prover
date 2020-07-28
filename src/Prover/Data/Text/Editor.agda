module Prover.Data.Text.Editor where

open import Prover.Category
  using (Category)
open import Prover.Category.Split.Base
  using (SplitFunction; split-function-from-retraction)
open import Prover.Category.Unit
  using (category-unit)
open import Prover.Client.Aeson
  using (Value)
open import Prover.Data.Text
  using (Text; TextWith)
open import Prover.Editor
  using (EventStack; EventStackMap; SimpleEditor; SplitEditor)
open import Prover.Editor.Base
  using (BaseEventStack; BaseEventStackMap; BaseViewStack; SimpleBaseEditor)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatViewStack; FlatViewStackMap)
open import Prover.Editor.Flatten
  using (base-event-stack-flatten; base-event-stack-flatten-lift;
    base-view-stack-flatten-lift; split-editor-flatten)
open import Prover.Editor.Lift
  using (event-stack-lift; event-stack-map-lift; simple-editor-lift)
open import Prover.Editor.Map
  using (flat-editor-map-event; flat-editor-map-view; split-editor-map-event;
    split-editor-map-simple)
open import Prover.Editor.Unit
  using (split-editor-unit)
open import Prover.View.Command
  using (CommandFlatViewStack; command)
open import Prover.View.Text
  using (PlainTextBaseViewStack; PlainTextFlatViewStack; PlainTextViewStack)
open import Prover.Prelude

open Vec
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

TextWithBaseEventStack
  : (Char → Bool)
  → BaseEventStack
TextWithBaseEventStack p
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → TextWithEvent p
  }

TextBaseEventStack
  : BaseEventStack
TextBaseEventStack
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → TextEvent
  }

TextWithEventStack
  : (Char → Bool)
  → EventStack
TextWithEventStack p
  = event-stack-lift
    (TextWithBaseEventStack p)

TextEventStack
  : EventStack
TextEventStack
  = event-stack-lift
    TextBaseEventStack

TextFlatEventStack
  : FlatEventStack
TextFlatEventStack
  = base-event-stack-flatten
    TextBaseEventStack

-- ### State

TextWithState
  : (Char → Bool)
  → Set
TextWithState p
  = Any (Vec (CharWith p))

-- ### Pure

TextWithCategory
  : (Char → Bool)
  → Category
TextWithCategory p
  = category-unit (TextWith p)

TextCategory
  : Category
TextCategory
  = category-unit Text

-- ## Encode

-- ### Encode

encode-text
  : Text
  → Value
encode-text (any cs)
  = Value.string (Vec.to-builtin cs)

-- ### Decode

decode-text
  : Value
  → Maybe Text
decode-text (Value.string (cons c cs))
  = just (any (cons c (List.from-builtin cs)))
decode-text _
  = nothing

-- ### Valid

decode-encode-text
  : (t : Text)
  → decode-text (encode-text t) ≡ just t
decode-encode-text (any (cons c cs))
  with List.from-builtin (List.to-builtin cs)
  | List.from-builtin-to-builtin cs
... | _ | refl
  = refl

-- ## Editors

-- ### Base

-- #### Module

module TextWithSimpleBaseEditor
  (p : Char → Bool)
  where

  -- ##### Types

  open BaseViewStack PlainTextBaseViewStack
  open BaseEventStack (TextWithBaseEventStack p)

  State
    : Set
  State
    = List (CharWith p)

  -- ##### State

  StatePath
    : State
    → Set
  StatePath (any {n} _)
    = Fin (suc n)

  initial
    : State
  initial
    = any []

  initial-path
    : (s : State)
    → StatePath s
  initial-path _
    = Fin.maximum

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
  initial-path-with _ Direction.right
    = Fin.maximum

  -- ##### Draw

  draw
    : State
    → View
  draw (any cs)
    = any (Vec.map CharWith.char cs)

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
  handle (any cs) zero delete-previous
    = (any cs , zero)
  handle (any cs@(_ ∷ _)) (suc k) delete-previous
    = (any (Vec.delete cs k) , k)
  handle (any []) _ delete-next
    = (any [] , zero)
  handle (any (_ ∷ cs)) zero delete-next
    = (any cs , zero)
  handle (any (c ∷ cs)) (suc k) delete-next
    with handle (any cs) k delete-next
  ... | ((any cs') , k')
    = (any (c ∷ cs') , suc k')
  handle (any cs) k (insert c)
    = (any (Vec.insert cs k c) , suc k)

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
  handle-direction-valid _ Direction.right
    = Fin.increment-maximum

-- #### Function

text-with-simple-base-editor
  : (p : Char → Bool)
  → SimpleBaseEditor
    PlainTextBaseViewStack
    (TextWithBaseEventStack p)
    (TextWithState p)
text-with-simple-base-editor p
  = record {TextWithSimpleBaseEditor p}

-- ### Simple

text-with-simple-editor
  : (p : Char → Bool)
  → SimpleEditor
    PlainTextViewStack
    (TextWithEventStack p)
    (TextWithState p)
text-with-simple-editor p
  = simple-editor-lift
    (text-with-simple-base-editor p)

-- ### Split

-- #### TextWith

module TextWithSplitFunction
  (p : Char → Bool)
  where

  partial-function
    : TextWithState p
    → Maybe (TextWith p)
  partial-function (any [])
    = nothing
  partial-function (any cs@(_ ∷ _))
    = just (any cs)

  function
    : TextWith p
    → TextWithState p
  function (any cs)
    = any cs

  valid
    : (t : TextWith p)
    → partial-function (function t) ≡ just t
  valid (any (_ ∷ _))
    = refl

text-with-split-function
  : (p : Char → Bool)
  → SplitFunction
    (TextWithState p)
    (TextWith p)
text-with-split-function p
  = record {TextWithSplitFunction p}

text-with-split-editor
  : (p : Char → Bool)
  → SplitEditor
    PlainTextViewStack
    (TextWithEventStack p)
    (TextWithCategory p)
text-with-split-editor p
  = split-editor-unit (text-with-split-function p)
  $ text-with-simple-editor p

-- #### Text

module TextBaseEventStackMap where

  mode
    : BaseEventStack.Mode (TextWithBaseEventStack (const true))
    → BaseEventStack.Mode TextBaseEventStack
  mode
    = id

  event
    : (m : BaseEventStack.Mode (TextWithBaseEventStack (const true)))
    → BaseEventStack.Event TextBaseEventStack (mode m)
    → BaseEventStack.Event (TextWithBaseEventStack (const true)) m
  event _ delete-previous
    = delete-previous
  event _ delete-next
    = delete-next
  event _ (insert c)
    = insert (char-with c refl)

text-base-event-stack-map
  : BaseEventStackMap
    (TextWithBaseEventStack (const true))
    TextBaseEventStack
text-base-event-stack-map
  = record {TextBaseEventStackMap}

text-event-stack-map
  : EventStackMap
    (TextWithEventStack (const true))
    TextEventStack
text-event-stack-map
  = event-stack-map-lift
    text-base-event-stack-map

text-split-editor
  : SplitEditor
    PlainTextViewStack
    TextEventStack
    TextCategory
text-split-editor
  = split-editor-map-event text-event-stack-map
  $ split-editor-map-simple (split-function-from-retraction Text.retraction)
  $ text-with-split-editor (const true)

-- ### Flat

text-flat-editor
  : FlatEditor
    PlainTextFlatViewStack
    TextFlatEventStack
    Text
text-flat-editor
  = flat-editor-map-view (base-view-stack-flatten-lift PlainTextBaseViewStack)
  $ flat-editor-map-event (base-event-stack-flatten-lift TextBaseEventStack)
  $ split-editor-flatten
  $ text-split-editor

-- ## Command

module CommandFlatStackMap
  (p : String)
  where

  view-with
    : (v : FlatViewStack.View PlainTextFlatViewStack)
    → FlatViewStack.ViewPath PlainTextFlatViewStack v
    → FlatViewStack.View CommandFlatViewStack
  view-with (any cs) nothing
    = command p (any (Vec.snoc cs ' '))
  view-with t (just _)
    = command p t

  view-path
    : (v : FlatViewStack.View PlainTextFlatViewStack)
    → (vp : FlatViewStack.ViewPath PlainTextFlatViewStack v)
    → FlatViewStack.ViewPath CommandFlatViewStack (view-with v vp)
  view-path _ nothing
    = Fin.maximum
  view-path _ (just k)
    = k

-- Takes a prompt string, not including colon or space.
command-flat-stack-map
  : String
  → FlatViewStackMap
    PlainTextFlatViewStack
    CommandFlatViewStack
command-flat-stack-map p
  = record {CommandFlatStackMap p}

-- Takes a prompt string, not including colon or space.
command-flat-editor
  : String
  → FlatEditor
    CommandFlatViewStack
    TextFlatEventStack
    Text
command-flat-editor s
  = flat-editor-map-view (command-flat-stack-map s)
  $ text-flat-editor

