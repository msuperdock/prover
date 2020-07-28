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
  using (Dec; Decidable; Symmetric)

-- ## Definition

FinSet
  : Set
  → Set
FinSet A
  = Collection (Equal A)

-- ## Module

module FinSet where

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

  -- ### Construction

  module _
    {A : Set}
    where

    empty
      : FinSet A
    empty
      = Collection.empty

  -- ### Equality

  module _
    {A : Set}
    where

    decidable
      : Decidable (Equal A)
      → Decidable (Equal (FinSet A))
    decidable
      = Collection.decidable

  -- ### Membership

  module _
    {A : Set}
    where

    open Collection public
      using (Member; member)

    IsMember
      : FinSet A
      → A
      → Set
    IsMember
      = Collection.IsMember

    is-member?
      : (xs : FinSet A)
      → Decidable (Equal A)
      → (x : A)
      → Dec (IsMember xs x)
    is-member?
      = Collection.is-member?

    find-member
      : (xs : FinSet A)
      → Decidable (Equal A)
      → A
      → Maybe (Member xs)
    find-member xs d x
      = Collection.find-member xs (Bool.from-decidable d x)

