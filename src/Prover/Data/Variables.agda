module Prover.Data.Variables where

open import Prover.Data.Collection.Named
  using (NamedCollection)
open import Prover.Data.Equal
  using (Equal; _≡_)
open import Prover.Data.Maybe
  using (just)
open import Prover.Data.Relation
  using (Dec; Decidable)
open import Prover.Data.Variable
  using (Variable; _≟_var)

-- ## Definition

Variables
  : Set
Variables
  = NamedCollection Variable.name

-- ## Module

module Variables where

  open NamedCollection Variable.name public
    using (Member; empty; insert; lookup; lookup-member; lookup-member-nothing;
      member)

  -- ### Equality

  _≟_vars
    : Decidable (Equal Variables)
  _≟_vars
    = NamedCollection.decidable Variable.name _≟_var

  -- ### Membership

  var_∈_
    : Variable
    → Variables
    → Set
  var v ∈ vs
    = NamedCollection.IsMember Variable.name vs v

  var_∈?_
    : (v : Variable)
    → (vs : Variables)
    → Dec (var v ∈ vs)
  var v ∈? vs
    = NamedCollection.is-member? Variable.name vs _≟_var v

  lookup-member-just
    : (vs : Variables)
    → (v : Variable)
    → {m : Member vs}
    → .(var v ∈ vs)
    → lookup-member vs (Variable.name v) ≡ just m
    → v ≡ Member.value m
  lookup-member-just vs
    = NamedCollection.lookup-member-just Variable.name vs _≟_var

-- ## Exports

open Variables public
  using (_≟_vars; var_∈_; var_∈?_)

