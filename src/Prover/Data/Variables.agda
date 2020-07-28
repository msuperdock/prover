module Prover.Data.Variables where

open import Prover.Data.Variable
  using (Variable; _≟_var)
open import Prover.Prelude

-- ## Definition

Variables
  : Set
Variables
  = FinSet Variable

-- ## Module

module Variables where

  -- ### Interface

  is-member
    : Variables
    → Variable
    → Bool
  is-member vs
    = FinSet.is-member vs _≟_var

  insert
    : (vs : Variables)
    → (v : Variable)
    → is-member vs v ≡ false
    → Variables
  insert vs
    = FinSet.insert vs _≟_var

  -- ### Construction

  empty
    : Variables
  empty
    = FinSet.empty

  -- ### Membership

  open FinSet public
    using (Member; member)

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
    = FinSet.is-member? vs _≟_var v

  _≟_vars
    : Decidable (Equal Variables)
  _≟_vars
    = FinSet.decidable _≟_var

  find-member
    : (vs : Variables)
    → Variable
    → Maybe (Member vs)
  find-member vs
    = FinSet.find-member vs _≟_var

-- ## Exports

open Variables public
  using (var_∈_; var_∈?_; _≟_vars)

