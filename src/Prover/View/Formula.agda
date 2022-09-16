module Prover.View.Formula where

open import Prover.Data.Maybe
  using (Maybe)
open import Prover.View.RichText
  using (RichText; RichTextPath)

-- ## Definitions

FormulaView
  : Set
FormulaView
  = RichText

FormulaViewPath
  : FormulaView
  → Set
FormulaViewPath f
  = Maybe (RichTextPath f)

