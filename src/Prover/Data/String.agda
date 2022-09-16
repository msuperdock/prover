module Prover.Data.String where

open import Prover.Data.Char
  using (Char)
open import Prover.Data.Function
  using (_∘_)
open import Prover.Data.List
  using (List)

import Agda.Builtin.String
  as Builtin

open Builtin
  using () renaming
  ( primStringToList
    to to-list'
  )

-- ## Definition

String
  = Builtin.String

-- ## Module

module String where

  to-list
    : String
    → List Char
  to-list
    = List.from-builtin
    ∘ to-list'

