module Prover.Prelude.FinSet where

open import Prover.Prelude.Bool
  using (Bool; false; true)
open import Prover.Prelude.Collection
  using (Collection)
open import Prover.Prelude.Decidable
  using (Dec; Decidable)
open import Prover.Prelude.Empty
  using (⊥-elim)
open import Prover.Prelude.Equality
  using (_≡_)
open import Prover.Prelude.Function
  using (id)
open import Prover.Prelude.Inspect
  using ([_]; inspect)
open import Prover.Prelude.Maybe
  using (just; nothing)

FinSet
  : {A : Set}
  → Decidable A
  → Set
FinSet p
  = Collection id p

-- ## Module

module FinSet where

  open Collection public
    using (IsMember; Member; empty; lookup-member; member)

  -- ### Interface

  module _
    {A : Set}
    {p : Decidable A}
    where

    is-member
      : FinSet p
      → A
      → Bool
    is-member xs x
      with Collection.lookup xs x
    ... | nothing
      = false
    ... | just _
      = true
  
    insert
      : (xs : FinSet p)
      → (x : A)
      → is-member xs x ≡ false
      → FinSet p
    insert xs x q
      with Collection.lookup xs x
      | inspect (Collection.lookup xs) x
    ... | nothing | [ r ]
      = Collection.insert xs x r
    ... | just _ | _
      = ⊥-elim (Bool.true≢false q)

  -- ### Equality

  module _
    {A : Set}
    {p : Decidable A}
    where

    decidable
      : Decidable (FinSet p)
    decidable
      = Collection.decidable p

  -- ### Membership

  module _
    {A : Set}
    {p : Decidable A}
    where

    is-member?
      : (xs : FinSet p)
      → (x : A)
      → Dec (IsMember xs x)
    is-member?
      = Collection.is-member? p

