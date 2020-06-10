module Prover.View.Command where

open import Prover.Editor.Flat
  using (FlatViewStack)
open import Prover.View.Text
  using (PlainText; PlainTextPath)
open import Prover.Prelude

-- ## Definitions

record Command
  : Set
  where

  constructor

    command

  field

    -- Not including colon or space.
    prompt
      : String

    text
      : PlainText

CommandPath
  : Command
  → Set
CommandPath (command _ t)
  = PlainTextPath t

-- ## Stacks

CommandFlatViewStack
  : FlatViewStack
CommandFlatViewStack
  = record
  { View
    = Command
  ; ViewPath
    = CommandPath
  }

