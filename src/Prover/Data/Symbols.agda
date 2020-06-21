module Prover.Data.Symbols where

open import Prover.Data.Identifier
  using (Identifier; _≟_idn)
open import Prover.Data.Symbol
  using (Symbol; _≟_sym; _≟_sym?)
open import Prover.Prelude

-- ## Definition

Symbols
  : Set
Symbols
  = Collection {A = Any Symbol} (Symbol.name ∘ Any.value) _≟_idn

-- ## Module

module Symbols where

  open Collection public
    using (empty; lookup; to-vec)

  -- ### Interface

  module _
    {a : ℕ}
    where

    insert
      : (ss : Symbols)
      → (s : Symbol a)
      → lookup ss (Symbol.name s) ≡ nothing
      → Symbols
    insert ss
      = Collection.insert ss ∘ any

  -- ### Membership

  sym_∈_
    : {a : ℕ}
    → Symbol a
    → Symbols
    → Set
  sym s ∈ ss
    = Collection.IsMember ss (any s)
  
  sym_∈?_
    : {a : ℕ}
    → (s : Symbol a)
    → (ss : Symbols)
    → Dec (sym s ∈ ss)
  sym s ∈? ss
    = Collection.is-member? _≟_sym? ss (any s)

  record Member
    (ss : Symbols)
    : Set
    where

    constructor
    
      member

    field

      {arity}
        : ℕ

      symbol
        : Symbol arity

      is-member
        : sym symbol ∈ ss

  lookup-member
    : (ss : Symbols)
    → Identifier
    → Maybe (Member ss)
  lookup-member ss n
    with Collection.lookup-member ss n
  ... | nothing
    = nothing
  ... | just (Collection.member (any s) p)
    = just (member s p)

  lookup-member-any
    : {ss : Symbols}
    → {m : Member ss}
    → {a : ℕ}
    → (s : Symbol a)
    → .(sym s ∈ ss)
    → lookup-member ss (Symbol.name s) ≡ just m
    → Equal (Any Symbol) (Any Symbol) (any s) (any (Member.symbol m))
  lookup-member-any {ss = ss} s p _
    with Collection.lookup-member ss (Symbol.name s)
    | inspect (Collection.lookup-member ss) (Symbol.name s)
  ... | just _ | [ q ]
    with Collection.lookup-member-eq (any s) (recompute (sym s ∈? ss) p) q
  lookup-member-any _ _ refl | _ | _ | refl
    = refl

  lookup-member-arity
    : {ss : Symbols}
    → {m : Member ss}
    → {a : ℕ}
    → (s : Symbol a)
    → .(sym s ∈ ss)
    → lookup-member ss (Symbol.name s) ≡ just m
    → a ≡ Member.arity m
  lookup-member-arity s p q
    with lookup-member-any s p q
  ... | refl
    = refl

  lookup-member-eq
    : {ss : Symbols}
    → {m : Member ss}
    → {a : ℕ}
    → (s : Symbol a)
    → .(sym s ∈ ss)
    → lookup-member ss (Symbol.name s) ≡ just m
    → s ≅ Member.symbol m
  lookup-member-eq s p q
    with lookup-member-any s p q
  ... | refl
    = refl

  lookup-member-nothing
    : (ss : Symbols)
    → (n : Identifier)
    → lookup-member ss n ≡ nothing
    → lookup ss n ≡ nothing
  lookup-member-nothing ss n p
    with Collection.lookup-member ss n
    | inspect (Collection.lookup-member ss) n
  ... | nothing | [ q ]
    = Collection.lookup-member-nothing ss n q

-- ## Exports

open Symbols public
  using (sym_∈_; sym_∈?_)

