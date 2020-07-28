module Prover.View.Interface where

open import Prover.View.Command
  using (Command; CommandPath)
open import Prover.View.Window
  using (Window; WindowPath)
open import Prover.Prelude

open Vec
  using (_!_)

record Interface
  : Set
  where

  constructor

    interface

  field

    {length}
      : ℕ
  
    command
      : Maybe Command

    windows
      : Vec Window length

data InterfacePath
  : Interface
  → Set
  where

  nothing
    : {n : ℕ}
    → {ws : Vec Window n}
    → InterfacePath (interface nothing ws)

  window
    : {n : ℕ}
    → {ws : Vec Window n}
    → (k : Fin n)
    → WindowPath (ws ! k)
    → InterfacePath (interface nothing ws)

  command
    : {n : ℕ}
    → {c : Command}
    → {ws : Vec Window n}
    → CommandPath c
    → InterfacePath (interface (just c) ws)
  
