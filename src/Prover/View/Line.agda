module Prover.View.Line where

open import Prover.Data.Bool
  using (Bool)
open import Prover.View.RichText
  using (RichText; RichTextPath)

-- ## Definitions

record Line
  : Set
  where

  constructor
  
    line

  field

    -- If false, a flag is shown in left margin.
    status
      : Bool

    text
      : RichText

LinePath
  : Line
  → Set
LinePath (line _ t)
  = RichTextPath t

