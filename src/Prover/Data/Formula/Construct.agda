module Prover.Data.Formula.Construct where

open import Prover.Data.Associativity
  using (Associativity)
open import Prover.Data.Precedence
  using (Precedence; _<_prc)
open import Prover.Data.Symbol
  using (Symbol; SymbolValid; symbol; tt)
open import Prover.Prelude

open SymbolValid

-- ## Definition

module Internal where

  data Construct
    : Set
    where
  
    atom
      : Construct
  
    symbol
      : {a : ℕ}
      → Symbol a
      → Construct

  construct-to-pair
    : Construct
    → Maybe (Precedence × Associativity)
  construct-to-pair atom
    = nothing
  construct-to-pair (symbol (symbol neither _ _ _ _))
    = nothing
  construct-to-pair (symbol (symbol left _ _ ip _))
    = just (If.value ip , Associativity.left)
  construct-to-pair (symbol (symbol right _ _ ip _))
    = just (If.value ip , Associativity.right)
  construct-to-pair (symbol (symbol both _ _ ip ia))
    = just (If.value ip , If.value ia)
  
  construct-is-left-valid
    : {a : ℕ}
    → (s : Symbol a)
    → Symbol.HasLeft s
    → Construct
    → Bool
  construct-is-left-valid s _ c
    with construct-to-pair (symbol s)
    | construct-to-pair c
  ... | _ | nothing
    = true
  ... | nothing | _
    = false
  ... | just (p₁ , a₁) | just (p₂ , a₂)
    with Precedence.compare p₁ p₂ | a₁ | a₂
  ... | less _ _ _ | _ | _
    = true
  ... | equal _ _ _ | Associativity.left | Associativity.left
    = true
  ... | equal _ _ _ | _ | _
    = false
  ... | greater _ _ _ | _ | _
    = false
  
  record ConstructLeftValid
    {a : ℕ}
    (s : Symbol a)
    (c : Construct)
    : Set
    where

    constructor

      construct-left-valid

    field

      has-left
        : Symbol.HasLeft s

      valid
        : T (construct-is-left-valid s has-left c)

  construct-left-valid?
    : {a : ℕ}
    → (s : Symbol a)
    → (c : Construct)
    → Dec (ConstructLeftValid s c)
  construct-left-valid? s c
    with Symbol.has-left? s
  ... | no ¬hl
    = no (¬hl ∘ ConstructLeftValid.has-left)
  ... | yes hl
    with Bool.to-dec (construct-is-left-valid s hl c)
  ... | no ¬lv
    = no (¬lv ∘ ConstructLeftValid.valid)
  ... | yes lv
    = yes (construct-left-valid hl lv)

  construct-is-right-valid
    : {a : ℕ}
    → (s : Symbol a)
    → Symbol.HasRight s
    → Construct
    → Bool
  construct-is-right-valid s _ c
    with construct-to-pair (symbol s)
    | construct-to-pair c
  ... | _ | nothing
    = true
  ... | nothing | _
    = false
  ... | just (p₁ , a₁) | just (p₂ , a₂)
    with Precedence.compare p₁ p₂ | a₁ | a₂
  ... | less _ _ _ | _ | _
    = true
  ... | equal _ _ _ | Associativity.right | Associativity.right
    = true
  ... | equal _ _ _ | _ | _
    = false
  ... | greater _ _ _ | _ | _
    = false
  
  record ConstructRightValid
    {a : ℕ}
    (s : Symbol a)
    (c : Construct)
    : Set
    where

    constructor

      construct-right-valid

    field

      has-right
        : Symbol.HasRight s

      valid
        : T (construct-is-right-valid s has-right c)

  construct-right-valid?
    : {a : ℕ}
    → (s : Symbol a)
    → (c : Construct)
    → Dec (ConstructRightValid s c)
  construct-right-valid? s c
    with Symbol.has-right? s
  ... | no ¬hr
    = no (¬hr ∘ ConstructRightValid.has-right)
  ... | yes hr
    with Bool.to-dec (construct-is-right-valid s hr c)
  ... | no ¬rv
    = no (¬rv ∘ ConstructRightValid.valid)
  ... | yes rv
    = yes (construct-right-valid hr rv)

  construct-left-valid-right-valid'
    : {a₁ a₂ : ℕ}
    → (s₁ : Symbol a₁)
    → (s₂ : Symbol a₂)
    → (c : Construct)
    → (rv : ConstructRightValid s₁ (symbol s₂))
    → ConstructLeftValid s₂ c
    → T (construct-is-right-valid s₁ (ConstructRightValid.has-right rv) c)
  construct-left-valid-right-valid' s₁ s₂ c
    (construct-right-valid tt rv) (construct-left-valid tt _)
    with construct-to-pair (symbol s₁)
    | construct-to-pair (symbol s₂)
    | construct-to-pair c
  ... | _ | _ | nothing
    = tt
  ... | just (p₁ , a₁) | just (p₂ , a₂) | just (p₃ , a₃)
    with Nat.compare p₁ p₂
    | Nat.compare p₂ p₃
    | Nat.compare p₁ p₃
  ... | _ | _ | less _ _ _
    = tt
  ... | less p _ _ | less q _ _ | equal ¬r _ _
    = ⊥-elim (¬r (Precedence.transitive p q))
  ... | less p _ _ | less q _ _ | greater ¬r _ _
    = ⊥-elim (¬r (Precedence.transitive p q))
  ... | less p _ _ | equal _ q _ | equal ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → p₁ < x prc) (sym q) p))
  ... | less p  _ _ | equal _ q _ | greater ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → p₁ < x prc) (sym q) p))
  ... | equal _ p _ | less q _ _ | greater ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → x < p₃ prc) p q))
  ... | equal _ p _ | less q _ _ | equal ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → x < p₃ prc) p q))
  ... | equal _ p _ | equal _ q _ | greater _ ¬r _
    = ⊥-elim (¬r (trans p q))
  ... | equal _ _ _ | equal _ _ _ | equal _ _ _
    with a₁ | a₂
  ... | Associativity.left | Associativity.left
    = rv
  
  construct-left-valid-right-valid
    : {a₁ a₂ : ℕ}
    → (s₁ : Symbol a₁)
    → (s₂ : Symbol a₂)
    → (c : Construct)
    → ConstructRightValid s₁ (symbol s₂)
    → ConstructLeftValid s₂ c
    → ConstructRightValid s₁ c
  construct-left-valid-right-valid s₁ s₂ c rv@(construct-right-valid hr _) lv
    = construct-right-valid hr (construct-left-valid-right-valid' s₁ s₂ c rv lv)

  construct-right-valid-left-valid'
    : {a₁ a₂ : ℕ}
    → (s₁ : Symbol a₁)
    → (s₂ : Symbol a₂)
    → (c : Construct)
    → (lv : ConstructLeftValid s₁ (symbol s₂))
    → ConstructRightValid s₂ c
    → T (construct-is-left-valid s₁ (ConstructLeftValid.has-left lv) c)
  construct-right-valid-left-valid' s₁ s₂ c
    (construct-left-valid tt lv) (construct-right-valid tt _)
    with construct-to-pair (symbol s₁)
    | construct-to-pair (symbol s₂)
    | construct-to-pair c
  ... | _ | _ | nothing
    = tt
  ... | just (p₁ , a₁) | just (p₂ , a₂) | just (p₃ , a₃)
    with Nat.compare p₁ p₂
    | Nat.compare p₂ p₃
    | Nat.compare p₁ p₃
  ... | _ | _ | less _ _ _
    = tt
  ... | less p _ _ | less q _ _ | equal ¬r _ _
    = ⊥-elim (¬r (Precedence.transitive p q))
  ... | less p _ _ | less q _ _ | greater ¬r _ _
    = ⊥-elim (¬r (Precedence.transitive p q))
  ... | less p _ _ | equal _ q _ | equal ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → p₁ < x prc) (sym q) p))
  ... | less p  _ _ | equal _ q _ | greater ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → p₁ < x prc) (sym q) p))
  ... | equal _ p _ | less q _ _ | greater ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → x < p₃ prc) p q))
  ... | equal _ p _ | less q _ _ | equal ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → x < p₃ prc) p q))
  ... | equal _ p _ | equal _ q _ | greater _ ¬r _
    = ⊥-elim (¬r (trans p q))
  ... | equal _ _ _ | equal _ _ _ | equal _ _ _
    with a₁ | a₂
  ... | Associativity.right | Associativity.right
    = lv

  construct-right-valid-left-valid
    : {a₁ a₂ : ℕ}
    → (s₁ : Symbol a₁)
    → (s₂ : Symbol a₂)
    → (c : Construct)
    → ConstructLeftValid s₁ (symbol s₂)
    → ConstructRightValid s₂ c
    → ConstructLeftValid s₁ c
  construct-right-valid-left-valid s₁ s₂ c lv@(construct-left-valid hl _) rv
    = construct-left-valid hl (construct-right-valid-left-valid' s₁ s₂ c lv rv)

  data LeftSubconstruct
    : Construct
    → Construct
    → Set
    where
  
    reflexive
      : {c : Construct}
      → LeftSubconstruct c c

    recursive
      : {a : ℕ}
      → {s : Symbol a}
      → {c₁ c₂ : Construct}
      → ConstructLeftValid s c₁
      → LeftSubconstruct c₁ c₂
      → LeftSubconstruct (symbol s) c₂

  data RightSubconstruct
    : Construct
    → Construct
    → Set
    where
  
    reflexive
      : {c : Construct}
      → RightSubconstruct c c

    recursive
      : {a : ℕ}
      → {s : Symbol a}
      → {c₁ c₂ : Construct}
      → ConstructRightValid s c₁
      → RightSubconstruct c₁ c₂
      → RightSubconstruct (symbol s) c₂

  left-subconstruct-right-valid
    : {a : ℕ}
    → {c₁ c₂ : Construct}
    → LeftSubconstruct c₁ c₂
    → (s : Symbol a)
    → ConstructRightValid s c₁
    → ConstructRightValid s c₂
  left-subconstruct-right-valid reflexive _ rv
    = rv
  left-subconstruct-right-valid (recursive {s = s₂} {c₁ = c} lv ls) s₁ rv
    = left-subconstruct-right-valid ls s₁
      (construct-left-valid-right-valid s₁ s₂ c rv lv)

  right-subconstruct-left-valid
    : {a : ℕ}
    → {c₁ c₂ : Construct}
    → RightSubconstruct c₁ c₂
    → (s : Symbol a)
    → ConstructLeftValid s c₁
    → ConstructLeftValid s c₂
  right-subconstruct-left-valid reflexive _ lv
    = lv
  right-subconstruct-left-valid (recursive {s = s₂} {c₁ = c} rv rs) s₁ lv
    = right-subconstruct-left-valid rs s₁
      (construct-right-valid-left-valid s₁ s₂ c lv rv)

-- ## Modules

-- ### Construct

Construct
  : Set
Construct
  = Internal.Construct

module Construct where

  open Internal.Construct public

  open Internal public using () renaming
    ( ConstructLeftValid
      to LeftValid
    ; ConstructRightValid
      to RightValid
    ; construct-left-valid
      to left-valid
    ; construct-left-valid?
      to left-valid?
    ; construct-right-valid
      to right-valid
    ; construct-right-valid?
      to right-valid?
    )

-- ### LeftSubconstruct

LeftSubconstruct
  : Construct
  → Construct
  → Set
LeftSubconstruct
  = Internal.LeftSubconstruct

module LeftSubconstruct where

  open Internal.LeftSubconstruct public

  open Internal public using () renaming
    ( left-subconstruct-right-valid
      to right-valid
    )

-- ### RightSubconstruct

RightSubconstruct
  : Construct
  → Construct
  → Set
RightSubconstruct
  = Internal.RightSubconstruct

module RightSubconstruct where

  open Internal.RightSubconstruct public

  open Internal public using () renaming
    ( right-subconstruct-left-valid
      to left-valid
    )

