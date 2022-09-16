module Prover.View.Interface where

open import Prover.Data.Fin
  using (Fin)
open import Prover.Data.List
  using (List; _!_)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.View.Command
  using (Command; CommandPath)
open import Prover.View.Window
  using (Window; WindowPath)

-- ## Definitions

record Interface
  : Set
  where

  constructor

    interface

  field

    command
      : Maybe Command

    windows
      : List Window

data InterfacePath
  : Interface
  → Set
  where

  nothing
    : {ws : List Window}
    → InterfacePath (interface nothing ws)

  window
    : {ws : List Window}
    → (k : Fin (List.length ws))
    → WindowPath (ws ! k)
    → InterfacePath (interface nothing ws)

  command
    : {c : Command}
    → {ws : List Window}
    → CommandPath c
    → InterfacePath (interface (just c) ws)
  
