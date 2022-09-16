module Prover.Data.List where

open import Prover.Data.Any
  using (Any; any)
open import Prover.Data.Bool
  using (Bool; F; T)
open import Prover.Data.Empty
  using (¬_)
open import Prover.Data.Equal
  using (Equal; _≡_; refl)
open import Prover.Data.Fin
  using (Fin)
open import Prover.Data.Function
  using (_∘_)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Nat
  using (_≟_nat)
open import Prover.Data.Relation
  using (Dec; Decidable)
open import Prover.Data.Sigma
  using (Σ)
open import Prover.Data.Vec
  using (Subvec; Vec; cons; nil)

import Data.List
  as List''

-- ## Definition

List
  = List''.List

open List'' public
  using (List')

-- ## Module

module List where

  open List''.List public

  -- ### Interface

  snoc
    : {A : Set}
    → List A
    → A
    → List A
  snoc (any xs) x
    = any (Vec.snoc xs x)

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

  find
    : {A : Set}
    → List A
    → (A → Bool)
    → Maybe A
  find (any xs)
    = Vec.find xs

  find-nothing
    : {A : Set}
    → (xs : List A)
    → (f : A → Bool)
    → find xs f ≡ nothing
    → (k : Fin (length xs))
    → F (f (xs ! k))
  find-nothing (any xs)
    = Vec.find-nothing xs

  find-just
    : {A : Set}
    → {y : A}
    → (xs : List A)
    → (f : A → Bool)
    → find xs f ≡ just y
    → T (f y)
  find-just (any xs)
    = Vec.find-just xs

  find-cons
    : {A : Set}
    → (xs : List A)
    → (x : A)
    → (f : A → Bool)
    → T (f x)
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

  -- ### Equality

  module _
    {A : Set}
    where

    decidable
      : Decidable (Equal A)
      → Decidable (Equal (List A))
    decidable d
      = Any.decidable (Vec A) _≟_nat (Vec.decidable d)

    cons-equal
      : {x₁ x₂ : A}
      → {xs₁ xs₂ : List A}
      → x₁ ≡ x₂
      → xs₁ ≡ xs₂
      → Equal (List A) (x₁ ∷ xs₁) (x₂ ∷ xs₂)
    cons-equal refl refl
      = refl

  -- ### Conversion

  module _
    {A : Set}
    where

    to-vec
      : (xs : List A)
      → Vec A (length xs)
    to-vec (any xs)
      = xs

    from-to-builtin
      : (xs : List A)
      → from-builtin (to-builtin xs) ≡ xs
    from-to-builtin (any nil)
      = refl
    from-to-builtin (any (cons _ xs))
      = cons-equal refl (from-to-builtin xs)

  -- ### Membership

  open Vec public
    using (is-member; member)

  IsMember
    : {A : Set}
    → List A
    → A
    → Set
  IsMember (any xs) y
    = Vec.IsMember xs y

  is-member?
    : {A : Set}
    → (xs : List A)
    → Decidable (Equal A)
    → (y : A)
    → Dec (IsMember xs y)
  is-member? (any xs)
    = Vec.is-member? xs

  find-is-member
    : {A : Set}
    → {y : A}
    → (xs : List A)
    → (f : A → Bool)
    → find xs f ≡ just y
    → IsMember xs y
  find-is-member (any xs)
    = Vec.find-is-member xs

  is-member-find
    : {A : Set}
    → {y : A}
    → (xs : List A)
    → (f : A → Bool)
    → T (f y)
    → IsMember xs y
    → z ∈ A × find xs f ≡ just z
  is-member-find (any xs)
    = Vec.is-member-find xs

  Member
    : {A : Set}
    → List A
    → Set
  Member (any xs)
    = Vec.Member xs

  module Member
    = Vec.Member

  find-member
    : {A : Set}
    → (xs : List A)
    → (A → Bool)
    → Maybe (Member xs)
  find-member (any xs)
    = Vec.find-member xs

  find-member-nothing
    : {A : Set}
    → (xs : List A)
    → (f : A → Bool)
    → (x : A)
    → T (f x)
    → find-member xs f ≡ nothing
    → ¬ IsMember xs x
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
      : {xs₂ : List A}
      → {x : A}
      → (xs₁ : List A)
      → IsMember xs₂ x
      → xs₁ ⊆ xs₂
      → x ∷ xs₁ ⊆ xs₂
    ⊆-cons-left (any xs₁)
      = Vec.⊆-cons-left xs₁

-- ## Exports

open List public
  using (Sublist; []; _∷_; _!_)

