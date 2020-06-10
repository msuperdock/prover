module Prover.Data.Variables where

open import Prover.Data.Variable
  using (Variable; _≟_var)
open import Prover.Prelude

-- ## Definition

Variables
  : Set
Variables
  = FinSet _≟_var

-- ## Module

module Variables where

  open FinSet public
    using (Member; empty; insert; is-member; lookup-member; member; to-vec)

  -- ### Equality

  _≟_vars
    : Decidable Variables
  _≟_vars
    = FinSet.decidable
  
  -- ### Membership

  var_∈_
    : Variable
    → Variables
    → Set
  var v ∈ vs
    = FinSet.IsMember vs v
  
  var_∈?_
    : (v : Variable)
    → (vs : Variables)
    → Dec (var v ∈ vs)
  var v ∈? vs
    = FinSet.is-member? vs v

-- ## Exports

open Variables public
  using (_≟_vars; var_∈_; var_∈?_)

