module Prover.Data.Symbol where

open import Prover.Data.Associativity
  using (Associativity; _≟_ass)
open import Prover.Data.Identifier
  using (Identifier; _≟_idn)
open import Prover.Data.Precedence
  using (Precedence; _≟_prc)
open import Prover.Data.Token
  using (Token; _≟_tkn)
open import Prover.Prelude

-- ## Definition

data SymbolValid
  : Bool
  → Bool
  → ℕ
  → ℕ
  → Set
  where

  neither
    : {ca : ℕ}
    → SymbolValid false false ca ca

  left
    : {ca : ℕ}
    → SymbolValid true false ca (suc ca)

  right
    : {ca : ℕ}
    → SymbolValid false true ca (suc ca)

  both
    : {ca : ℕ}
    → SymbolValid true true ca (suc (suc ca))

module _Symbol where

  record Symbol
    (a : ℕ)
    : Set
    where

    constructor
      
      symbol

    field

      {has-left}
        : Bool

      {has-right}
        : Bool

      {center-arity}
        : ℕ

      valid
        : SymbolValid has-left has-right center-arity a

      name
        : Identifier

      tokens
        : Vec Token (suc center-arity)

      precedence
        : If Precedence (has-left ∨ has-right)

      associativity
        : If Associativity (has-left ∧ has-right)

Symbol
  : ℕ
  → Set
Symbol
  = _Symbol.Symbol

open _Symbol public
  using (symbol)

-- ## Module

module Symbol where

  open _Symbol.Symbol public

  data HasLeft
    {a : ℕ}
    : Symbol a
    → Set
    where

    tt
      : {hr : Bool}
      → {ca : ℕ}
      → {v : SymbolValid true hr ca a}
      → {n : Identifier}
      → {ts : Vec Token (suc ca)}
      → {ip : If Precedence (true ∨ hr)}
      → {ia : If Associativity (true ∧ hr)}
      → HasLeft (symbol v n ts ip ia)

  data HasRight
    {a : ℕ}
    : Symbol a
    → Set
    where

    tt
      : {hl : Bool}
      → {ca : ℕ}
      → {v : SymbolValid hl true ca a}
      → {n : Identifier}
      → {ts : Vec Token (suc ca)}
      → {ip : If Precedence (hl ∨ true)}
      → {ia : If Associativity (hl ∧ true)}
      → HasRight (symbol v n ts ip ia)

  has-left?
    : {a : ℕ}
    → (s : Symbol a)
    → Dec (HasLeft s)
  has-left? (symbol {has-left = false} _ _ _ _ _)
    = no (λ ())
  has-left? (symbol {has-left = true} _ _ _ _ _)
    = yes tt

  has-right?
    : {a : ℕ}
    → (s : Symbol a)
    → Dec (HasRight s)
  has-right? (symbol {has-right = false} _ _ _ _ _)
    = no (λ ())
  has-right? (symbol {has-right = true} _ _ _ _ _)
    = yes tt

  data ¬HasLeft
    {a : ℕ}
    : Symbol a
    → Set
    where

    tt
      : {hr : Bool}
      → {ca : ℕ}
      → {v : SymbolValid false hr ca a}
      → {n : Identifier}
      → {ts : Vec Token (suc ca)}
      → {ip : If Precedence (false ∨ hr)}
      → {ia : If Associativity (false ∧ hr)}
      → ¬HasLeft (symbol v n ts ip ia)

  data ¬HasRight
    {a : ℕ}
    : Symbol a
    → Set
    where

    tt
      : {hl : Bool}
      → {ca : ℕ}
      → {v : SymbolValid hl false ca a}
      → {n : Identifier}
      → {ts : Vec Token (suc ca)}
      → {ip : If Precedence (hl ∨ false)}
      → {ia : If Associativity (hl ∧ false)}
      → ¬HasRight (symbol v n ts ip ia)

  valid-eq
    : {a ca : ℕ}
    → {hl hr : Bool}
    → (v₁ v₂ : SymbolValid hl hr ca a)
    → v₁ ≡ v₂
  valid-eq neither neither
    = refl
  valid-eq left left
    = refl
  valid-eq right right
    = refl
  valid-eq both both
    = refl

  _≟_tkns
    : {n : ℕ}
    → Decidable (Vec Token n)
  _≟_tkns
    = Vec.decidable _≟_tkn
  
  _≟_prc?
    : {b : Bool}
    → Decidable (If Precedence b)
  _≟_prc?
    = If.decidable _≟_prc

  _≟_ass?
    : {b : Bool}
    → Decidable (If Associativity b)
  _≟_ass?
    = If.decidable _≟_ass

  _≟_sym
    : {a : ℕ}
    → Decidable (Symbol a)
  _≟_sym
    (symbol {hl₁} {hr₁} {ca₁} v₁ n₁ ts₁ ip₁ ia₁)
    (symbol {hl₂} {hr₂} {ca₂} v₂ n₂ ts₂ ip₂ ia₂)
    with hl₁ ≟ hl₂ bool
    | hr₁ ≟ hr₂ bool
    | ca₁ ≟ ca₂ nat

  ... | no ¬p | _ | _
    = no (λ {refl → ¬p refl})
  ... | _ | no ¬p | _
    = no (λ {refl → ¬p refl})
  ... | _ | _ | no ¬p
    = no (λ {refl → ¬p refl})
  ... | yes refl | yes refl | yes refl
    with valid-eq v₁ v₂
    | n₁ ≟ n₂ idn
    | ts₁ ≟ ts₂ tkns
    | ip₁ ≟ ip₂ prc?
    | ia₁ ≟ ia₂ ass?

  ... | _ | no ¬p | _ | _ | _
    = no (λ {refl → ¬p refl})
  ... | _ | _ | no ¬p | _ | _
    = no (λ {refl → ¬p refl})
  ... | _ | _ | _ | no ¬p | _
    = no (λ {refl → ¬p refl})
  ... | _ | _ | _ | _ | no ¬p
    = no (λ {refl → ¬p refl})
  ... | refl | yes refl | yes refl | yes refl | yes refl
    = yes refl

  _≟_sym?
    : Decidable (Any Symbol)
  _≟_sym?
    = Any.decidable _≟_nat _≟_sym

-- ## Exports

open Symbol public
  using (_≟_sym; _≟_sym?; tt)

