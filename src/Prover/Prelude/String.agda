module Prover.Prelude.String where

open import Prover.Prelude.Char
  using (Char)
open import Prover.Prelude.Function
  using (_∘_)
open import Prover.Prelude.List
  using (List)

import Agda.Builtin.String as Builtin

open Builtin public
  using (String)
open Builtin using () renaming
  ( primStringFromList
    to from-list'
  ; primStringToList
    to to-list'
  )

module String where

  from-list
    : List Char
    → String
  from-list
    = from-list'
    ∘ List.to-builtin

  to-list
    : String
    → List Char
  to-list
    = List.from-builtin
    ∘ to-list'

