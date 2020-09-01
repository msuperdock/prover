module Prover.Function.Bool.List where

open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Prelude

open List
  using ([]; _∷_)

-- ## BoolFunction

bool-function-list
  : {A : Set}
  → BoolFunction A
  → BoolFunction (List A)
bool-function-list _ []
  = true
bool-function-list f (x ∷ xs)
  = f x ∧ bool-function-list f xs

