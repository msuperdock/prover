module Prover.Prelude.List where

open import Prover.Prelude.Any
  using (Any; any)
open import Prover.Prelude.Bool
  using (Bool; F; T; true)
open import Prover.Prelude.Empty
  using (¬_)
open import Prover.Prelude.Equal
  using (Equal; _≡_; refl)
open import Prover.Prelude.Fin
  using (Fin)
open import Prover.Prelude.Function
  using (_∘_)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Nat
  using (ℕ; _≟_nat)
open import Prover.Prelude.Relation
  using (Dec; Decidable)
open import Prover.Prelude.Sigma
  using (Σ)
open import Prover.Prelude.Vec
  using (Subvec; Vec; cons; nil)

import Agda.Builtin.List
  as Builtin

-- ## Definition

List
  : Set
  → Set
List A
  = Any (Vec A)

-- ## Builtin

List'
  : Set
  → Set
List'
  = Builtin.List

module List' where

  open Builtin.List public using () renaming
    ( []
      to nil
    ; _∷_
      to cons
    )

  open Builtin.List public using () renaming
    ( []
      to []'
    ; _∷_
      to _∷'_
    )

open List' public
  using (cons; nil)

-- ## Module

module List where

  -- ### Interface

  infixr 5 _∷_
  
  pattern []
    = any nil
  pattern _∷_ x xs
    = any (cons x xs)

  length
    : {A : Set}
    → List A
    → ℕ
  length (any {n} _)
    = n
  
  lookup
    : {A : Set}
    → (xs : List A)
    → Fin (length xs)
    → A
  lookup (any xs) k
    = Vec.lookup xs k
  
  _!_
    : {A : Set}
    → (xs : List A)
    → Fin (length xs)
    → A
  _!_
    = lookup
  
  map
    : {A B : Set}
    → (A → B)
    → List A
    → List B
  map f (any xs)
    = any (Vec.map f xs)

  append
    : {A : Set}
    → List A
    → List A
    → List A
  append [] ys
    = ys
  append (x ∷ xs) ys
    = x ∷ append xs ys

  concat
    : {A : Set}
    → List (List A)
    → List A
  concat []
    = []
  concat (xs ∷ xss)
    = append xs (concat xss)

  -- ### Construction

  module _
    {A : Set}
    where

    snoc
      : List A
      → A
      → List A
    snoc (any xs) x
      = any (Vec.snoc xs x)

  -- ### Conversion

  module _
    {A : Set}
    where

    from-builtin
      : List' A
      → List A
    from-builtin nil
      = []
    from-builtin (cons x xs)
      = x ∷ from-builtin xs

    to-builtin
      : List A
      → List' A
    to-builtin (any xs)
      = Vec.to-builtin xs
  
    from-builtin-to-builtin
      : (xs : List A)
      → from-builtin (to-builtin xs) ≡ xs
    from-builtin-to-builtin (any nil)
      = refl
    from-builtin-to-builtin (any (cons _ xs))
      with from-builtin (to-builtin xs)
      | from-builtin-to-builtin xs
    ... | _ | refl
      = refl

  -- ### Equality

  module _
    {A : Set}
    where

    decidable
      : Decidable (Equal A)
      → Decidable (Equal (List A))
    decidable d
      = Any.decidable (Vec A) _≟_nat (Vec.decidable d)

  -- ### Membership

  module _
    {A : Set}
    where

    open Vec public
      using (member)

    IsMember
      : List A
      → A
      → Set
    IsMember (any xs) y
      = Vec.IsMember xs y

    is-member?
      : (xs : List A)
      → Decidable (Equal A)
      → (y : A)
      → Dec (IsMember xs y)
    is-member? (any xs)
      = Vec.is-member? xs

    Member
      : List A
      → Set
    Member (any xs)
      = Vec.Member xs

    module Member where

      open Vec.Member public

  -- ### Properties

  lookup-map
    : {A B : Set}
    → (f : A → B)
    → (xs : List A)
    → (k : Fin (length xs))
    → map f xs ! k ≡ f (xs ! k)
  lookup-map f (any xs)
    = Vec.lookup-map f xs

  -- ### Sublist

  module _
    {A : Set}
    where

    Sublist
      : List A
      → List A
      → Set
    Sublist (any xs) (any ys)
      = Subvec xs ys
  
    infix 4 _⊆_
  
    _⊆_
      : List A
      → List A
      → Set
    _⊆_
      = Sublist
  
    ⊆-refl
      : (xs : List A)
      → xs ⊆ xs
    ⊆-refl (any xs)
      = Vec.⊆-refl xs
  
    ⊆-trans
      : (xs₁ xs₂ xs₃ : List A)
      → xs₁ ⊆ xs₂
      → xs₂ ⊆ xs₃
      → xs₁ ⊆ xs₃
    ⊆-trans (any xs₁) (any xs₂) (any xs₃)
      = Vec.⊆-trans xs₁ xs₂ xs₃

    ⊆-nil
      : (xs : List A)
      → [] ⊆ xs
    ⊆-nil (any xs)
      = Vec.⊆-nil xs

    ⊆-cons
      : (x : A)
      → (xs : List A)
      → xs ⊆ x ∷ xs
    ⊆-cons x (any xs)
      = Vec.⊆-cons x xs

    ⊆-cons-left
      : (xs₁ xs₂ : List A)
      → (x : A)
      → IsMember xs₂ x
      → xs₁ ⊆ xs₂
      → x ∷ xs₁ ⊆ xs₂
    ⊆-cons-left (any xs₁) (any xs₂)
      = Vec.⊆-cons-left xs₁ xs₂

  -- ### Find

  find
    : {A : Set}
    → List A
    → (A → Bool)
    → Maybe A
  find (any xs)
    = Vec.find xs

  find-member
    : {A : Set}
    → (xs : List A)
    → (A → Bool)
    → Maybe (Member xs)
  find-member (any xs)
    = Vec.find-member xs

  find-true
    : {A : Set}
    → {y : A}
    → (xs : List A)
    → (f : A → Bool)
    → find xs f ≡ just y
    → T (f y)
  find-true (any xs)
    = Vec.find-true xs

  find-is-member
    : {A : Set}
    → {y : A}
    → (xs : List A)
    → (f : A → Bool)
    → find xs f ≡ just y
    → IsMember xs y
  find-is-member (any xs)
    = Vec.find-is-member xs

  find-¬is-member
    : {A : Set}
    → (xs : List A)
    → (f : A → Bool)
    → (x : A)
    → T (f x)
    → find xs f ≡ nothing
    → ¬ IsMember xs x
  find-¬is-member (any xs)
    = Vec.find-¬is-member xs

  find-nothing
    : {A : Set}
    → (xs : List A)
    → (f : A → Bool)
    → find xs f ≡ nothing
    → (k : Fin (length xs))
    → F (f (xs ! k))
  find-nothing (any xs)
    = Vec.find-nothing xs

  find-member-nothing
    : {A : Set}
    → (xs : List A)
    → (f : A → Bool)
    → find-member xs f ≡ nothing
    → find xs f ≡ nothing
  find-member-nothing (any xs)
    = Vec.find-member-nothing xs

  find-member-just
    : {A : Set}
    → (xs : List A)
    → {m : Member xs}
    → (f : A → Bool)
    → find-member xs f ≡ just m
    → find xs f ≡ just (Member.value m)
  find-member-just (any xs)
    = Vec.find-member-just xs

  find-cons
    : {A : Set}
    → (xs : List A)
    → (x : A)
    → (f : A → Bool)
    → f x ≡ true
    → find (x ∷ xs) f ≡ just x
  find-cons (any xs)
    = Vec.find-cons xs

  find-map
    : {A B : Set}
    → {y : A}
    → (f : A → B)
    → (xs : List A)
    → (g : B → Bool)
    → find xs (g ∘ f) ≡ just y
    → find (map f xs) g ≡ just (f y)
  find-map f (any xs)
    = Vec.find-map f xs

  member-find
    : {A : Set}
    → {y : A}
    → (xs : List A)
    → (f : A → Bool)
    → T (f y)
    → IsMember xs y
    → z ∈ A × find xs f ≡ just z
  member-find (any xs)
    = Vec.member-find xs

-- ## Exports

open List public
  using (Sublist)

