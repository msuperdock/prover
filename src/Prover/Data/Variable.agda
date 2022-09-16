module Prover.Data.Variable where

open import Prover.Data.Equal
  using (Equal; refl)
open import Prover.Data.Relation
  using (Decidable; no; yes)
open import Prover.Data.Text
  using (Text; _≟_txt)
open import Prover.Data.Token
  using (Token; _≟_tkn)

-- ## Definition

record Variable'
  : Set
  where

  constructor

    variable'

  field

    name
      : Text

    token
      : Token

Variable
  = Variable'

-- ## Module

module Variable where

  open Variable' public

  _≟_var
    : Decidable (Equal Variable)
  variable' n₁ t₁ ≟ variable' n₂ t₂ var
    with n₁ ≟ n₂ txt
    | t₁ ≟ t₂ tkn
  ... | no ¬p | _
    = no (λ {refl → ¬p refl})
  ... | _ | no ¬p
    = no (λ {refl → ¬p refl})
  ... | yes refl | yes refl
    = yes refl

-- ## Exports

open Variable public
  using (_≟_var)

