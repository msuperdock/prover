module Prover.View.Line where

open import Prover.View.Text
  using (RichText; RichTextPath)
open import Prover.Prelude

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

