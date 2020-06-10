module Prover.Data.Rules where

open import Prover.Data.Identifier
  using (_≟_idn)
open import Prover.Data.Rule
  using (Rule; _≟_rul?)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Prelude

-- ## Definition

Rules
  : Symbols
  → Set
Rules ss
  = Collection {A = Any (Rule ss)} (Rule.name ∘ Any.value) _≟_idn

-- ## Module

module Rules where

  open Collection public
    using (Member; empty; lookup; lookup-member; member; to-vec)

  -- ### Interface

  insert
    : {ss : Symbols}
    → {a : ℕ}
    → (rs : Rules ss)
    → (r : Rule ss a)
    → lookup rs (Rule.name r) ≡ nothing
    → Rules ss
  insert rs
    = Collection.insert rs ∘ any

  -- ### Membership

  module _
    {ss : Symbols}
    {a : ℕ}
    where

    rul_∈_
      : Rule ss a
      → Rules ss
      → Set
    rul r ∈ rs
      = Collection.IsMember rs (any r)
  
    rul_∈?_
      : (r : Rule ss a)
      → (rs : Rules ss)
      → Dec (rul r ∈ rs)
    rul r ∈? rs
      = Collection.is-member? _≟_rul? rs (any r)

-- ## Exports

open Rules public
  using (rul_∈_; rul_∈?_)

