module Prover.Data.Symbols where

open import Prover.Data.Collection.Named
  using (NamedCollection)
open import Prover.Data.Equal
  using (_≡_)
open import Prover.Data.Maybe
  using (just)
open import Prover.Data.Relation
  using (Dec)
open import Prover.Data.Symbol
  using (Symbol; _≟_sym)

-- ## Definition

Symbols
  : Set
Symbols
  = NamedCollection Symbol.name

-- ## Module

module Symbols where

  open NamedCollection Symbol.name public
    using (Member; empty; insert; lookup; lookup-member; lookup-member-nothing;
      member)

  -- ### Membership

  sym_∈_
    : Symbol
    → Symbols
    → Set
  sym s ∈ ss
    = NamedCollection.IsMember Symbol.name ss s

  sym_∈?_
    : (s : Symbol)
    → (ss : Symbols)
    → Dec (sym s ∈ ss)
  sym s ∈? ss
    = NamedCollection.is-member? Symbol.name ss _≟_sym s

  lookup-member-just
    : (ss : Symbols)
    → (s : Symbol)
    → {m : Member ss}
    → .(sym s ∈ ss)
    → lookup-member ss (Symbol.name s) ≡ just m
    → s ≡ Member.value m
  lookup-member-just ss
    = NamedCollection.lookup-member-just Symbol.name ss _≟_sym

-- ## Exports

open Symbols public
  using (sym_∈_; sym_∈?_)

