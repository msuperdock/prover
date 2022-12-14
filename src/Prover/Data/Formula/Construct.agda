module Prover.Data.Formula.Construct where

open import Prover.Data.Associativity
  using (Associativity)
open import Prover.Data.Bool
  using (Bool; T; false; true)
open import Prover.Data.Empty
  using (⊥-elim)
open import Prover.Data.Equal
  using (refl; rewrite'; sym; trans)
open import Prover.Data.Function
  using (_∘_)
open import Prover.Data.If
  using (If)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Nat
  using (module Nat; ℕ; _<_nat)
open import Prover.Data.Relation
  using (Dec; τ₁; τ₂; τ₃; no; yes)
open import Prover.Data.Sigma
  using (_×_; _,_)
open import Prover.Data.Symbol
  using (Symbol; SymbolValid; symbol)

open SymbolValid

-- ## Internal

module Internal where

  data Construct
    : Set
    where
  
    atom
      : Construct
  
    symbol
      : Symbol
      → Construct

  construct-to-pair
    : Construct
    → Maybe (ℕ × Associativity)
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
    : (s : Symbol)
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
    with Nat.compare p₁ p₂
    | a₁
    | a₂
  ... | τ₁ _ _ _ | _ | _
    = true
  ... | τ₂ _ _ _ | Associativity.left | Associativity.left
    = true
  ... | τ₂ _ _ _ | _ | _
    = false
  ... | τ₃ _ _ _ | _ | _
    = false
  
  record ConstructLeftValid
    (s : Symbol)
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
    : (s : Symbol)
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
    : (s : Symbol)
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
    with Nat.compare p₁ p₂
    | a₁
    | a₂
  ... | τ₁ _ _ _ | _ | _
    = true
  ... | τ₂ _ _ _ | Associativity.right | Associativity.right
    = true
  ... | τ₂ _ _ _ | _ | _
    = false
  ... | τ₃ _ _ _ | _ | _
    = false
  
  record ConstructRightValid
    (s : Symbol)
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
    : (s : Symbol)
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
    : (s₁ s₂ : Symbol)
    → (c : Construct)
    → (rv : ConstructRightValid s₁ (symbol s₂))
    → ConstructLeftValid s₂ c
    → T (construct-is-right-valid s₁ (ConstructRightValid.has-right rv) c)
  construct-left-valid-right-valid' s₁ s₂ c
    (construct-right-valid Symbol.tt rv)
    (construct-left-valid Symbol.tt _)
    with construct-to-pair (symbol s₁)
    | construct-to-pair (symbol s₂)
    | construct-to-pair c
  ... | _ | _ | nothing
    = refl
  ... | just (p₁ , a₁) | just (p₂ , a₂) | just (p₃ , _)
    with Nat.compare p₁ p₂
    | Nat.compare p₂ p₃
    | Nat.compare p₁ p₃
  ... | _ | _ | τ₁ _ _ _
    = refl
  ... | τ₁ p _ _ | τ₁ q _ _ | τ₂ ¬r _ _
    = ⊥-elim (¬r (Nat.<-trans p q))
  ... | τ₁ p _ _ | τ₁ q _ _ | τ₃ ¬r _ _
    = ⊥-elim (¬r (Nat.<-trans p q))
  ... | τ₁ p _ _ | τ₂ _ q _ | τ₂ ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → p₁ < x nat) (sym q) p))
  ... | τ₁ p  _ _ | τ₂ _ q _ | τ₃ ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → p₁ < x nat) (sym q) p))
  ... | τ₂ _ p _ | τ₁ q _ _ | τ₃ ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → x < p₃ nat) p q))
  ... | τ₂ _ p _ | τ₁ q _ _ | τ₂ ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → x < p₃ nat) p q))
  ... | τ₂ _ p _ | τ₂ _ q _ | τ₃ _ ¬r _
    = ⊥-elim (¬r (trans p q))
  ... | τ₂ _ _ _ | τ₂ _ _ _ | τ₂ _ _ _
    with a₁
    | a₂
  ... | Associativity.left | Associativity.left
    = rv
  
  construct-left-valid-right-valid
    : (s₁ s₂ : Symbol)
    → (c : Construct)
    → ConstructRightValid s₁ (symbol s₂)
    → ConstructLeftValid s₂ c
    → ConstructRightValid s₁ c
  construct-left-valid-right-valid s₁ s₂ c rv@(construct-right-valid hr _) lv
    = construct-right-valid hr (construct-left-valid-right-valid' s₁ s₂ c rv lv)

  construct-right-valid-left-valid'
    : (s₁ s₂ : Symbol)
    → (c : Construct)
    → (lv : ConstructLeftValid s₁ (symbol s₂))
    → ConstructRightValid s₂ c
    → T (construct-is-left-valid s₁ (ConstructLeftValid.has-left lv) c)
  construct-right-valid-left-valid' s₁ s₂ c
    (construct-left-valid Symbol.tt lv)
    (construct-right-valid Symbol.tt _)
    with construct-to-pair (symbol s₁)
    | construct-to-pair (symbol s₂)
    | construct-to-pair c
  ... | _ | _ | nothing
    = refl
  ... | just (p₁ , a₁) | just (p₂ , a₂) | just (p₃ , _)
    with Nat.compare p₁ p₂
    | Nat.compare p₂ p₃
    | Nat.compare p₁ p₃
  ... | _ | _ | τ₁ _ _ _
    = refl
  ... | τ₁ p _ _ | τ₁ q _ _ | τ₂ ¬r _ _
    = ⊥-elim (¬r (Nat.<-trans p q))
  ... | τ₁ p _ _ | τ₁ q _ _ | τ₃ ¬r _ _
    = ⊥-elim (¬r (Nat.<-trans p q))
  ... | τ₁ p _ _ | τ₂ _ q _ | τ₂ ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → p₁ < x nat) (sym q) p))
  ... | τ₁ p  _ _ | τ₂ _ q _ | τ₃ ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → p₁ < x nat) (sym q) p))
  ... | τ₂ _ p _ | τ₁ q _ _ | τ₃ ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → x < p₃ nat) p q))
  ... | τ₂ _ p _ | τ₁ q _ _ | τ₂ ¬r _ _
    = ⊥-elim (¬r (rewrite' (λ x → x < p₃ nat) p q))
  ... | τ₂ _ p _ | τ₂ _ q _ | τ₃ _ ¬r _
    = ⊥-elim (¬r (trans p q))
  ... | τ₂ _ _ _ | τ₂ _ _ _ | τ₂ _ _ _
    with a₁
    | a₂
  ... | Associativity.right | Associativity.right
    = lv

  construct-right-valid-left-valid
    : (s₁ s₂ : Symbol)
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
      : {s : Symbol}
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
      : {s : Symbol}
      → {c₁ c₂ : Construct}
      → ConstructRightValid s c₁
      → RightSubconstruct c₁ c₂
      → RightSubconstruct (symbol s) c₂

  left-subconstruct-right-valid
    : {c₁ c₂ : Construct}
    → LeftSubconstruct c₁ c₂
    → (s : Symbol)
    → ConstructRightValid s c₁
    → ConstructRightValid s c₂
  left-subconstruct-right-valid reflexive _ rv
    = rv
  left-subconstruct-right-valid (recursive {s = s₂} {c₁ = c} lv ls) s₁ rv
    = left-subconstruct-right-valid ls s₁
      (construct-left-valid-right-valid s₁ s₂ c rv lv)

  right-subconstruct-left-valid
    : {c₁ c₂ : Construct}
    → RightSubconstruct c₁ c₂
    → (s : Symbol)
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
  = Internal.Construct

module Construct where

  open Internal.Construct public

  open Internal public
    using () renaming
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
  = Internal.LeftSubconstruct

module LeftSubconstruct where

  open Internal.LeftSubconstruct public

  open Internal public
    using () renaming
    ( left-subconstruct-right-valid
      to right-valid
    )

-- ### RightSubconstruct

RightSubconstruct
  = Internal.RightSubconstruct

module RightSubconstruct where

  open Internal.RightSubconstruct public

  open Internal public
    using () renaming
    ( right-subconstruct-left-valid
      to left-valid
    )

