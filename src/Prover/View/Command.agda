module Prover.View.Command where

open import Prover.Data.Fin
  using (Fin)
open import Prover.Data.String
  using (String)
open import Prover.Data.Text
  using (Text)

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
      : Text

CommandPath
  : Command
  → Set
CommandPath (command _ t)
  = Fin (Text.length t)

