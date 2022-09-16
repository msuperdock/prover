module Prover.View.Window where

open import Prover.Data.Bool
  using (Bool)
open import Prover.Data.Fin
  using (Fin)
open import Prover.Data.List
  using (List; _!_)
open import Prover.Data.String
  using (String)
open import Prover.View.Line
  using (Line; LinePath)

-- ## Definitions

record Window
  : Set
  where

  constructor

    window

  field

    name
      : String

    -- Determines whether red or green light is shown in status bar.
    status
      : Bool

    lines
      : List Line

data WindowPath
  (w : Window)
  : Set
  where

  go
    : (k : Fin (List.length (Window.lines w)))
    → LinePath (Window.lines w ! k)
    → WindowPath w

