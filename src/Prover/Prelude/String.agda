module Prover.Prelude.String where

open import Prover.Prelude.Any
  using (Any)
open import Prover.Prelude.Char
  using (Char)
open import Prover.Prelude.Function
  using (_∘_)
open import Prover.Prelude.List
  using (List)
open import Prover.Prelude.Nat
  using (ℕ)
open import Prover.Prelude.Vec
  using (Vec)

import Agda.Builtin.String as Builtin

open Builtin public
  using (String)
open Builtin using () renaming
  ( primStringFromList
    to from-list
  ; primStringToList
    to to-list
  )

module String where

  from-vec
    : {n : ℕ}
    → Vec Char n
    → String
  from-vec
    = from-list
    ∘ List.from-vec

  to-vec
    : (s : String)
    → Any (Vec Char)
  to-vec
    = List.to-vec
    ∘ to-list

