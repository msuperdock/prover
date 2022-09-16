module Prover.Data.Metas where

open import Prover.Data.Bool
  using (Bool; false; true)
open import Prover.Data.List
  using (List; []; _∷_)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Nat
  using (suc; zero)
open import Prover.Data.Sigma
  using (_×_; _,_)

-- ## Definition

Metas
  : Set
Metas
  = List Bool

-- ## Module

module Metas where

  empty
    : Metas
  empty
    = []
  
  insert
    : Metas
    → Meta
    → Metas
  insert [] zero
    = true ∷ []
  insert [] (suc m)
    = false ∷ insert [] m
  insert (_ ∷ bs) zero
    = true ∷ bs
  insert (b ∷ bs) (suc m)
    = b ∷ insert bs m
  
  fresh
    : Metas
    → Meta × Metas
  fresh []
    = (zero , true ∷ [])
  fresh (false ∷ bs)
    = (zero , true ∷ bs)
  fresh (true  ∷ bs)
    with fresh bs
  ... | (m , bs')
    = (suc m , true ∷ bs')

