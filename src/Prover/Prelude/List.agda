module Prover.Prelude.List where

open import Prover.Prelude.Any
  using (Any; any)
open import Prover.Prelude.Bool
  using (Bool; F; T; true)
open import Prover.Prelude.Empty
  using (¬_)
open import Prover.Prelude.Equal
  using (Equal; _≡_; _≢_; refl; sub)
open import Prover.Prelude.Fin
  using (Fin; _<_fin; suc)
open import Prover.Prelude.Function
  using (_∘_; id)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Nat
  using (ℕ; _≟_nat; suc)
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
  length (any xs)
    = Vec.length xs
  
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
  
  update
    : {A : Set}
    → (xs : List A)
    → Fin (length xs)
    → A
    → List A
  update (any xs) k x
    = any (Vec.update xs k x)

  insert
    : {A : Set}
    → (xs : List A)
    → Fin (suc (length xs))
    → A
    → List A
  insert (any xs) k x
    = any (Vec.insert xs k x)

  delete
    : {A : Set}
    → (xs : List A)
    → Fin (length xs)
    → List A
  delete (any {suc _} xs) k
    = any (Vec.delete xs k)

  swap
    : {A : Set}
    → A
    → (xs : List A)
    → Fin (length xs)
    → List A
  swap x xs k
    = any (Vec.swap (cons x xs) k)

  map
    : {A B : Set}
    → (A → B)
    → List A
    → List B
  map f (any xs)
    = any (Vec.map f xs)

  map-maybe
    : {A B : Set}
    → (A → Maybe B)
    → List A
    → Maybe (List B)
  map-maybe f (any xs)
    = Maybe.map any (Vec.map-maybe f xs)

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

    to-vec
      : (xs : List A)
      → Vec A (length xs)
    to-vec (any xs)
      = xs

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
  
    from-to-builtin
      : (xs : List A)
      → from-builtin (to-builtin xs) ≡ xs
    from-to-builtin (any nil)
      = refl
    from-to-builtin (any (cons _ xs))
      = cons-equal refl (from-to-builtin xs)

  -- ### Membership

  module _
    {A : Set}
    where

    open Vec public
      using (is-member; member)

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

  lookup-update
    : {A : Set}
    → (xs : List A)
    → (k : Fin (length xs))
    → (y : A)
    → update xs k y ! k ≡ y
  lookup-update (any xs)
    = Vec.lookup-update xs

  lookup-update-other
    : {A : Set}
    → (xs : List A)
    → (k l : Fin (length xs))
    → (y : A)
    → k ≢ l
    → update xs k y ! l ≡ xs ! l
  lookup-update-other (any xs)
    = Vec.lookup-update-other xs

  lookup-insert
    : {A : Set}
    → (xs : List A)
    → (k : Fin (suc (length xs)))
    → (y : A)
    → insert xs k y ! k ≡ y
  lookup-insert (any xs)
    = Vec.lookup-insert xs

  lookup-insert-less
    : {A : Set}
    → (xs : List A)
    → {k : Fin (suc (length xs))}
    → (y : A)
    → (l : Fin (length xs))
    → Fin.lift l < k fin
    → insert xs k y ! Fin.lift l ≡ xs ! l
  lookup-insert-less (any xs)
    = Vec.lookup-insert-less xs

  lookup-insert-¬less
    : {A : Set}
    → (xs : List A)
    → (k : Fin (suc (length xs))) 
    → (y : A)
    → (l : Fin (length xs))
    → ¬ Fin.lift l < k fin
    → insert xs k y ! suc l ≡ xs ! l
  lookup-insert-¬less (any xs)
    = Vec.lookup-insert-¬less xs

  lookup-delete-less
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → {k l : Fin (length (x ∷ xs))}
    → {l' : Fin (length (delete (x ∷ xs) k))}
    → Fin.drop l ≡ just l'
    → l < k fin
    → delete (x ∷ xs) k ! l' ≡ (x ∷ xs) ! l
  lookup-delete-less x xs
    = Vec.lookup-delete-less (cons x xs)

  lookup-delete-¬less
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → (k : Fin (length (x ∷ xs)))
    → (l : Fin (length (delete (x ∷ xs) k)))
    → ¬ suc l < k fin
    → suc l ≢ k
    → delete (x ∷ xs) k ! l ≡ (x ∷ xs) ! suc l
  lookup-delete-¬less x xs
    = Vec.lookup-delete-¬less (cons x xs)

  lookup-swap₁
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → (k : Fin (length xs))
    → swap x xs k ! Fin.lift k ≡ (x ∷ xs) ! suc k
  lookup-swap₁ x xs
    = Vec.lookup-swap₁ (cons x xs)

  lookup-swap₂
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → (k : Fin (length xs))
    → swap x xs k ! suc k ≡ (x ∷ xs) ! Fin.lift k
  lookup-swap₂ x xs
    = Vec.lookup-swap₂ (cons x xs)

  lookup-swap₂'
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → {k : Fin (length xs)}
    → (k' : Fin (length (x ∷ xs)))
    → Fin.drop k' ≡ just k
    → swap x xs k ! suc k ≡ (x ∷ xs) ! k'
  lookup-swap₂' x xs
    = Vec.lookup-swap₂' (cons x xs)

  lookup-swap-less
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → (k : Fin (length xs)) 
    → {l : Fin (length (x ∷ xs))}
    → l < Fin.lift k fin
    → swap x xs k ! l ≡ (x ∷ xs) ! l
  lookup-swap-less x xs k
    = Vec.lookup-swap-less (cons x xs) k

  lookup-swap-greater
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → {k : Fin (length xs)}
    → {l : Fin (length (x ∷ xs))}
    → suc k < l fin
    → swap x xs k ! l ≡ (x ∷ xs) ! l
  lookup-swap-greater x xs
    = Vec.lookup-swap-greater (cons x xs)

  lookup-map
    : {A B : Set}
    → (f : A → B)
    → (xs : List A)
    → (k : Fin (length xs))
    → map f xs ! k ≡ f (xs ! k)
  lookup-map f (any xs)
    = Vec.lookup-map f xs

  map-equal
    : {A B : Set}
    → (f₁ f₂ : A → B)
    → ((x : A) → f₁ x ≡ f₂ x)
    → (xs : List A)
    → map f₁ xs ≡ map f₂ xs
  map-equal f₁ f₂ p (any xs)
    = sub any (Vec.map-equal f₁ f₂ p xs)

  map-identity
    : {A : Set}
    → (xs : List A)
    → map id xs ≡ xs
  map-identity (any xs)
    = sub any (Vec.map-identity xs)

  map-compose
    : {A B C : Set}
    → (f : B → C)
    → (g : A → B)
    → (xs : List A)
    → map (f ∘ g) xs ≡ map f (map g xs)
  map-compose f g (any xs)
    = sub any (Vec.map-compose f g xs)

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

  -- ### Find

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
    → IsMember xs y
  find-just (any xs)
    = Vec.find-just xs

  find-true
    : {A : Set}
    → {y : A}
    → (xs : List A)
    → (f : A → Bool)
    → find xs f ≡ just y
    → T (f y)
  find-true (any xs)
    = Vec.find-true xs

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

-- ## Exports

open List public
  using (Sublist)

