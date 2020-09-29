module Prover.Data.Number.Editor where

open import Prover.Data.Text.Editor
  using (TextWithEvent; text-with-simple-split-editor)
open import Prover.Editor
  using (EventStack; SimplePartialEditor; SimpleSplitEditor)
open import Prover.Editor.Base
  using (BaseEventStack)
open import Prover.Editor.Lift
  using (event-stack-lift)
open import Prover.Editor.Map
  using (simple-split-editor-map)
open import Prover.Function.Split
  using (split-function-from-retraction)
open import Prover.View.Text
  using (PlainTextViewStack)
open import Prover.Prelude

-- ## Types

-- ### Event

NumberEvent
  : Set
NumberEvent
  = TextWithEvent Char.is-digit

NumberBaseEventStack
  : BaseEventStack
NumberBaseEventStack
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → NumberEvent
  }

NumberEventStack
  : EventStack
NumberEventStack
  = event-stack-lift
    NumberBaseEventStack

-- ## Editors

-- ### SimpleSplitEditor

number-simple-split-editor
  : SimpleSplitEditor
    PlainTextViewStack
    NumberEventStack
    ℕ
number-simple-split-editor
  = simple-split-editor-map
    (split-function-from-retraction CharWith.retraction-digits)
  $ text-with-simple-split-editor Char.is-digit

-- ### SimplePartialEditor

number-simple-partial-editor
  : SimplePartialEditor
    PlainTextViewStack
    NumberEventStack
    ℕ
number-simple-partial-editor
  = SimpleSplitEditor.partial-editor number-simple-split-editor

