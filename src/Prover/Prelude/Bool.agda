module Prover.Prelude.Bool where

open import Prover.Prelude.Decidable
  using (Dec; Decidable; no; yes)
open import Prover.Prelude.Empty
  using (⊥; ⊥-elim)
open import Prover.Prelude.Equality
  using (_≡_; _≢_; refl)
open import Prover.Prelude.Function
  using (id)
open import Prover.Prelude.Unit
  using (⊤; tt)

import Agda.Builtin.Bool as Builtin

-- ## Definition

Bool
  : Set
Bool
  = Builtin.Bool

open Builtin.Bool public

-- ## Module

module Bool where

  open Builtin.Bool public

  -- ### Interface
  
  bool
    : {A : Set}
    → Bool
    → A
    → A
    → A
  bool false x _
    = x
  bool true _ x
    = x

  not
    : Bool
    → Bool
  not true
    = false
  not false
    = true
  
  infixr 5 _∨_
  infixr 6 _∧_
  
  _∨_
    : Bool
    → Bool
    → Bool
  false ∨ b
    = b
  true ∨ _
    = true

  _∧_
    : Bool
    → Bool
    → Bool
  false ∧ b
    = false
  true ∧ b
    = b
  
  -- ### Conversion

  T
    : Bool
    → Set
  T false
    = ⊥
  T true
    = ⊤
  
  from-dec
    : {A : Set}
    → Dec A
    → Bool
  from-dec (no _)
    = false
  from-dec (yes _)
    = true

  to-dec
    : (x : Bool)
    → Dec (T x)
  to-dec false
    = no id
  to-dec true
    = yes tt

  -- ### Equality

  _≟_bool
    : Decidable Bool
  
  false ≟ false bool
    = yes refl
  true ≟ true bool
    = yes refl
  
  false ≟ true bool
    = no (λ ())
  true ≟ false bool
    = no (λ ())

  -- ### Properties
  
  true≢false
    : true ≢ false
  true≢false ()
  
  ∧-elimination-left
    : {x y : Bool}
    → T (x ∧ y)
    → T x
  ∧-elimination-left {false} p
    = p
  ∧-elimination-left {true} p
    = tt
  
  ∧-elimination-right
    : {x y : Bool}
    → T (x ∧ y)
    → T y
  ∧-elimination-right {false} p
    = ⊥-elim p
  ∧-elimination-right {true} p
    = p
  
-- ## Exports

open Bool public
  using (T; _∨_; _∧_; _≟_bool; bool; not)

