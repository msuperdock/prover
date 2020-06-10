module Prover.Data.Number.Editor where

open import Prover.Category
  using (Category)
open import Prover.Category.Split.Unit
  using (split-functor-unit)
open import Prover.Category.Unit
  using (category-unit)
open import Prover.Data.Text.Editor
  using (TextWithEvent; TextViewStack; text-with-split-editor)
open import Prover.Editor
  using (EventStack; PartialEditor; SplitEditor; split-editor-partial)
open import Prover.Editor.Base
  using (BaseEventStack)
open import Prover.Editor.Lift
  using (event-stack-lift)
open import Prover.Editor.Map
  using (split-editor-map)
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

-- ### Pure

NumberCategory
  : Category
NumberCategory
  = category-unit ℕ

-- ## Editor

-- ### Split

number-split-editor
  : SplitEditor
    TextViewStack
    NumberEventStack
    NumberCategory
number-split-editor
  = split-editor-map
    (split-functor-unit (retraction-partial CharWith.retraction-digits))
  $ text-with-split-editor Char.is-digit

-- ### Partial

number-partial-editor
  : PartialEditor
    TextViewStack
    NumberEventStack
    ℕ
number-partial-editor
  = split-editor-partial number-split-editor
