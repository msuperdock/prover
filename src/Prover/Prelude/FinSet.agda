module Prover.Prelude.FinSet where

open import Prover.Prelude.Bool
  using (Bool; false; true)
open import Prover.Prelude.Collection
  using (Collection)
open import Prover.Prelude.Empty
  using (⊥-elim)
open import Prover.Prelude.Equal
  using (Equal; _≡_)
open import Prover.Prelude.Inspect
  using ([_]; inspect)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Relation
  using (Decidable; Symmetric)

-- ## Definition

FinSet
  : Set
  → Set
FinSet A
  = Collection (Equal A)

-- ## Module

module FinSet where

  open Collection public
    using (IsMember; Member; decidable; empty; is-member?; member)

  -- ### Interface

  module _
    {A : Set}
    where

    is-member
      : FinSet A
      → Decidable (Equal A)
      → A
      → Bool
    is-member xs d x
      with Collection.find xs (Bool.from-decidable d x)
    ... | nothing
      = false
    ... | just _
      = true

    insert
      : (xs : FinSet A)
      → (d : Decidable (Equal A))
      → (x : A)
      → is-member xs d x ≡ false
      → FinSet A
    insert xs d x p
      with Collection.find xs (Bool.from-decidable d x)
      | inspect (Collection.find xs) (Bool.from-decidable d x)
    ... | nothing | [ q ]
      = Collection.insert xs (Symmetric.equal A) d x q
    ... | just _ | _
      = ⊥-elim (Bool.true≢false p)

  -- ### Membership

  module _
    {A : Set}
    where

    find-member
      : (xs : FinSet A)
      → Decidable (Equal A)
      → A
      → Maybe (Member xs)
    find-member xs d x
      = Collection.find-member xs (Bool.from-decidable d x)

