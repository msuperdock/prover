module Prover.Data.Symbols where

open import Prover.Data.Identifier
  using (Identifier; _≟_idn)
open import Prover.Data.Symbol
  using (Symbol; _≟_sym; symbol)
open import Prover.Prelude

-- ## Utilities

relation
  : Relation Symbol
relation
  = Relation.map Symbol.name
    (Equal Identifier)

symmetric
  : Symmetric relation
symmetric
  = Symmetric.map Symbol.name
    (Equal Identifier)
    (Symmetric.equal Identifier)

transitive
  : Transitive relation
transitive
  = Transitive.map Symbol.name
    (Equal Identifier)
    (Transitive.equal Identifier)

decidable
  : Decidable relation
decidable
  = Decidable.map Symbol.name
    (Equal Identifier)
    _≟_idn

-- ## Definition

Symbols
  : Set
Symbols
  = Collection
    {A = Symbol}
    relation

-- ## Module

module Symbols where

  open Collection public
    using (Member; empty; member)

  -- ### Interface

  lookup
    : Symbols
    → Identifier
    → Maybe Symbol
  lookup ss n
    = Collection.find ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name)

  insert
    : (ss : Symbols)
    → (s : Symbol)
    → lookup ss (Symbol.name s) ≡ nothing
    → Symbols
  insert ss s
    = Collection.insert ss
      symmetric
      decidable s

  -- ### Membership

  sym_∈_
    : Symbol
    → Symbols
    → Set
  sym s ∈ ss
    = Collection.IsMember ss s

  sym_∈?_
    : (s : Symbol)
    → (ss : Symbols)
    → Dec (sym s ∈ ss)
  sym s ∈? ss
    = Collection.is-member? ss _≟_sym s

  lookup-member
    : (ss : Symbols)
    → Identifier
    → Maybe (Member ss)
  lookup-member ss n
    = Collection.find-member ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name)

  lookup-member-nothing
    : (ss : Symbols)
    → (s : Symbol)
    → lookup-member ss (Symbol.name s) ≡ nothing
    → ¬ sym s ∈ ss
  lookup-member-nothing ss s@(symbol _ n _ _ _)
    = Collection.find-member-nothing ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name) s
      (Bool.from-decidable-true _≟_idn n n refl)

  lookup-member-just
    : (ss : Symbols)
    → (s : Symbol)
    → {m : Member ss}
    → .(sym s ∈ ss)
    → lookup-member ss (Symbol.name s) ≡ just m
    → s ≡ Member.value m
  lookup-member-just ss s@(symbol _ n _ _ _) p q
    = Collection.find-member-just-eq ss
      (Bool.from-decidable _≟_idn n ∘ Symbol.name)
      (Unique.decidable symmetric transitive decidable s)
      (Bool.from-decidable-true _≟_idn n n refl)
      (Dec.recompute (sym s ∈? ss) p) q

-- ## Exports

open Symbols public
  using (sym_∈_; sym_∈?_)

