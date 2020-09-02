module Prover.Data.Symbols where

open import Prover.Data.Identifier
  using (Identifier; _≟_idn)
open import Prover.Data.Symbol
  using (Symbol; _≟_sym?)
open import Prover.Prelude

-- ## Utilities

relation
  : Relation (Any Symbol)
relation
  = Relation.map
    (Symbol.name ∘ Any.value)
    (Equal Identifier)

symmetric
  : Symmetric relation
symmetric
  = Symmetric.map
    (Symbol.name ∘ Any.value)
    (Equal Identifier)
    (Symmetric.equal Identifier)

transitive
  : Transitive relation
transitive
  = Transitive.map
    (Symbol.name ∘ Any.value)
    (Equal Identifier)
    (Transitive.equal Identifier)

decidable
  : Decidable relation
decidable
  = Decidable.map
    (Symbol.name ∘ Any.value)
    (Equal Identifier)
    _≟_idn

-- ## Definition

Symbols
  : Set
Symbols
  = Collection {A = Any Symbol} relation

-- ## Module

module Symbols where

  -- ### Interface

  lookup
    : Symbols
    → Identifier
    → Maybe (Any Symbol)
  lookup ss n
    = Collection.find ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name ∘ Any.value)

  insert
    : {a : ℕ}
    → (ss : Symbols)
    → (s : Symbol a)
    → lookup ss (Symbol.name s) ≡ nothing
    → Symbols
  insert ss s
    = Collection.insert ss symmetric decidable (any s)

  -- ### Construction

  open Collection public
    using (empty)

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
    = Collection.is-member? ss _≟_sym? (any s)

  record Member
    (ss : Symbols)
    : Set
    where

    constructor

      member

    field

      {arity}
        : ℕ

      value
        : Symbol arity

      is-member
        : sym value ∈ ss

  lookup-member
    : (ss : Symbols)
    → Identifier
    → Maybe (Member ss)
  lookup-member ss n
    with Collection.find-member ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name ∘ Any.value)
  ... | nothing
    = nothing
  ... | just (Collection.member (any s) p)
    = just (member s p)

  lookup-member-nothing
    : {a : ℕ}
    → (ss : Symbols)
    → (s : Symbol a)
    → lookup-member ss (Symbol.name s) ≡ nothing
    → ¬ sym s ∈ ss
  lookup-member-nothing ss s@(Symbol.symbol _ n _ _ _) _
    with Collection.find-member ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name ∘ Any.value)
    | inspect (Collection.find-member ss)
      (Bool.from-decidable _≟_idn n ∘ Symbol.name ∘ Any.value)
  ... | nothing | [ q ]
    = Collection.find-¬is-member ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name ∘ Any.value) (any s)
      (Bool.from-decidable-true _≟_idn n n refl)
    $ Collection.find-member-nothing ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name ∘ Any.value) q

  lookup-member-any
    : {ss : Symbols}
    → {m : Member ss}
    → {a : ℕ}
    → (s : Symbol a)
    → .(sym s ∈ ss)
    → lookup-member ss (Symbol.name s) ≡ just m
    → Equal (Any Symbol) (any s) (any (Member.value m))
  lookup-member-any {ss = ss} (Symbol.symbol _ n _ _ _) _ _
    with Collection.find-member ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name ∘ Any.value)
    | inspect (Collection.find-member ss)
      (Bool.from-decidable _≟_idn n ∘ Symbol.name ∘ Any.value)
  lookup-member-any {ss = ss} s@(Symbol.symbol _ n _ _ _) p refl
    | just _ | [ q ]
    = Collection.member-find-unique' ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name ∘ Any.value)
      (Unique.decidable symmetric transitive decidable (any s))
      (Bool.from-decidable-true decidable (any s) (any s) refl)
      (Dec.recompute (sym s ∈? ss) p) q

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
    → s ≅ Member.value m
  lookup-member-eq s p q
    with lookup-member-any s p q
  ... | refl
    = refl

-- ## Exports

open Symbols public
  using (sym_∈_; sym_∈?_)

