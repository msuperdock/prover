module Prover.Data.Number.Editor where

open import Prover.Data.Text.Editor
  using (TextWithEvent; simple-split-editor-text-with)
open import Prover.Editor
  using (EventStack; SimplePartialEditor; SimpleSplitEditor)
open import Prover.Editor.Base
  using (BaseEventStack)
open import Prover.Editor.Lift
  using (event-stack-lift)
open import Prover.Editor.Map
  using (simple-split-editor-map)
open import Prover.Function.Split
  using (retraction-split)
open import Prover.View.Text
  using (PlainTextViewStack)
open import Prover.Prelude

-- ## Types

-- ### Event

NumberEvent
  : Set
NumberEvent
  = TextWithEvent Char.is-digit

base-event-stack-number
  : BaseEventStack
base-event-stack-number
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → NumberEvent
  }

event-stack-number
  : EventStack
event-stack-number
  = event-stack-lift
    base-event-stack-number

-- ## Editors

-- ### SimpleSplitEditor

simple-split-editor-number
  : SimpleSplitEditor
    PlainTextViewStack
    event-stack-number
    ℕ
simple-split-editor-number
  = simple-split-editor-map
    (retraction-split CharWith.retraction-digits)
  $ simple-split-editor-text-with Char.is-digit

-- ### SimplePartialEditor

simple-partial-editor-number
  : SimplePartialEditor
    PlainTextViewStack
    event-stack-number
    ℕ
simple-partial-editor-number
  = SimpleSplitEditor.partial-editor simple-split-editor-number

