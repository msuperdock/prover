module Prover.Data.Metas where

open import Prover.Data.Meta
  using (Meta)
open import Prover.Prelude

open List
  using ([]; _∷_)

-- ## Definition

Metas
  : Set
Metas
  = List Bool

-- ## Module

module Metas where

  is-member
    : Metas
    → Meta
    → Bool
  is-member (true ∷ _) zero
    = true
  is-member (_ ∷ ms) (suc k)
    = is-member ms k
  is-member _ _
    = false
  
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

