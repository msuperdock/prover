module Prover.Event.Formula where

-- ## Definition

data FormulaEvent
  : Set
  where

  insert-parens
    : FormulaEvent

  insert-variable
    : FormulaEvent

  insert-symbol
    : FormulaEvent

