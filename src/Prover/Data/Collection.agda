module Prover.Data.Collection where

open import Prover.Data.Bool
  using (Bool; Unique; F; T)
open import Prover.Data.Empty
  using (¬_; ⊥-elim)
open import Prover.Data.Equal
  using (Equal; _≡_; refl; sub; sym; trans)
open import Prover.Data.Fin
  using (Fin; _≟_fin; suc; zero)
open import Prover.Data.Function
  using (_$_; _∘_)
open import Prover.Data.List
  using (List; Sublist; []; _∷_)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Nat
  using (ℕ)
open import Prover.Data.Relation
  using (Dec; Decidable; Injective; Relation; Symmetric; no; yes)
open import Prover.Data.Sigma
  using (Σ; _,_)

import Data.Collection
  as Collection'

-- ## Definition

Collection
  = Collection'.Collection

open Collection' public
  using (collection)

-- ## Module

module Collection where

  open Collection'.Collection public

  -- ### Interface

  length
    : {A : Set}
    → {R : Relation A}
    → Collection R
    → ℕ
  length (collection xs _)
    = List.length xs

  lookup
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → Fin (length xs)
    → A
  lookup (collection xs _)
    = List.lookup xs

  _!_
    = lookup

  valid'
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → (k₁ k₂ : Fin (length xs))
    → R (xs ! k₁) (xs ! k₂)
    → k₁ ≡ k₂
  valid' (collection _ p) k₁ k₂ r
    = Dec.recompute (k₁ ≟ k₂ fin) (p k₁ k₂ r)

  find
    : {A : Set}
    → {R : Relation A}
    → Collection R
    → (A → Bool)
    → Maybe A
  find (collection xs _)
    = List.find xs

  find-nothing
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → (f : A → Bool)
    → find xs f ≡ nothing
    → (k : Fin (length xs))
    → F (f (xs ! k))
  find-nothing (collection xs _)
    = List.find-nothing xs

  find-just
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → find xs f ≡ just y
    → T (f y)
  find-just (collection xs _)
    = List.find-just xs

  insert
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → Symmetric R
    → (d : Decidable R)
    → (x : A)
    → find xs (Bool.from-decidable d x) ≡ nothing
    → Collection R
  insert xs@(collection xs' _) s d x p
    = record
    { elements
      = x ∷ xs'
    ; valid
      = λ
      { zero zero _
        → refl
      ; zero (suc k₂) r
        → ⊥-elim (Bool.¬both
          (find-nothing xs (Bool.from-decidable d x) p k₂)
          (Bool.from-decidable-true d x (xs ! k₂) r))
      ; (suc k₁) zero r
        → ⊥-elim (Bool.¬both
          (find-nothing xs (Bool.from-decidable d x) p k₁)
          (Bool.from-decidable-true d x (xs ! k₁) (s (xs ! k₁) x r)))
      ; (suc k₁) (suc k₂) r
        → sub suc (valid' xs k₁ k₂ r)
      }
    }

  find-insert
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → (s : Symmetric R)
    → (d : Decidable R)
    → (x : A)
    → (p : find xs (Bool.from-decidable d x) ≡ nothing)
    → (f : A → Bool)
    → T (f x)
    → find (insert xs s d x p) f ≡ just x
  find-insert (collection xs _) _ _ x _
    = List.find-cons xs x

  map
    : {A B : Set}
    → {R : Relation A}
    → (S : Relation B)
    → (f : A → B)
    → Injective R S f
    → Collection R
    → Collection S
  map S f r xs@(collection xs' _)
    = record
    { elements
      = List.map f xs'
    ; valid
      = λ k₁ k₂
      → valid' xs k₁ k₂
      ∘ r (xs ! k₁) (xs ! k₂)
      ∘ Equal.rewrite₂ S
        (sym (List.lookup-map f xs' k₁))
        (sym (List.lookup-map f xs' k₂))
    }

  find-map
    : {A B : Set}
    → {y : A}
    → {R : Relation A}
    → (S : Relation B)
    → (f : A → B)
    → (i : Injective R S f)
    → (xs : Collection R)
    → (g : B → Bool)
    → find xs (g ∘ f) ≡ just y
    → find (map S f i xs) g ≡ just (f y)
  find-map _ f _ (collection xs _)
    = List.find-map f xs

  -- ### Equality

  module _
    {A : Set}
    {R : Relation A}
    where

    decidable
      : Decidable (Equal A)
      → Decidable (Equal (Collection R))
    decidable d (collection xs₁ _) (collection xs₂ _)
      with List.decidable d xs₁ xs₂
    ... | no ¬p
      = no λ {refl → ¬p refl}
    ... | yes refl
      = yes refl

  -- ### Construction

  module _
    {A : Set}
    {R : Relation A}
    where

    empty
      : Collection R
    empty
      = record
      { elements
        = []
      ; valid
        = λ ()
      }

  -- ### Membership

  open List public
    using (is-member; member)

  IsMember
    : {A : Set}
    → {R : Relation A}
    → Collection R
    → A
    → Set
  IsMember (collection xs _)
    = List.IsMember xs

  is-member?
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → Decidable (Equal A)
    → (x : A)
    → Dec (IsMember xs x)
  is-member? (collection xs _)
    = List.is-member? xs

  is-member-equal
    : {A : Set}
    → {R : Relation A}
    → {x₁ x₂ : A}
    → (xs : Collection R)
    → IsMember xs x₁
    → IsMember xs x₂
    → R x₁ x₂
    → x₁ ≡ x₂
  is-member-equal {R = R}
    xs@(collection xs' _)
    (is-member k₁ p₁)
    (is-member k₂ p₂) r
    = trans (sym p₁)
    $ trans (sub (List.lookup xs') (valid' xs k₁ k₂
      (Equal.rewrite₂ R p₁ p₂ r)))
    $ p₂

  find-is-member
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → find xs f ≡ just y
    → IsMember xs y
  find-is-member (collection xs _)
    = List.find-is-member xs

  is-member-find
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → T (f y)
    → IsMember xs y
    → z ∈ A × find xs f ≡ just z
  is-member-find (collection xs _)
    = List.is-member-find xs

  is-member-find-unique
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → Unique R f
    → T (f y)
    → IsMember xs y
    → find xs f ≡ just y
  is-member-find-unique {y = y} xs f u p m
    with is-member-find xs f p m
  ... | (z , q)
    = trans q
    $ sub just
    $ is-member-equal xs
      (find-is-member xs f q) m
      (u z y (find-just xs f q) p)

  Member
    : {A : Set}
    → {R : Relation A}
    → Collection R
    → Set
  Member (collection xs _)
    = List.Member xs

  module Member where
  
    open List.Member public

  find-member
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → (A → Bool)
    → Maybe (Member xs)
  find-member (collection xs _)
    = List.find-member xs

  find-member-nothing
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → (f : A → Bool)
    → (x : A)
    → T (f x)
    → find-member xs f ≡ nothing
    → ¬ IsMember xs x
  find-member-nothing (collection xs _)
    = List.find-member-nothing xs

  find-member-just'
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → {m : Member xs}
    → (f : A → Bool)
    → find-member xs f ≡ just m
    → find xs f ≡ just (Member.value m)
  find-member-just' (collection xs _)
    = List.find-member-just xs

  find-member-just
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → {m : Member xs}
    → (f : A → Bool)
    → Unique R f
    → T (f y)
    → IsMember xs y
    → find-member xs f ≡ just m
    → y ≡ Member.value m
  find-member-just xs f u p m q
    = Maybe.just-injective
    $ trans (sym (is-member-find-unique xs f u p m))
    $ find-member-just' xs f q

  -- ### Subcollection

  module _
    {A : Set}
    {R : Relation A}
    where

    Subcollection
      : Collection R
      → Collection R
      → Set
    Subcollection (collection xs₁ _) (collection xs₂ _)
      = Sublist xs₁ xs₂
    
    infix 4 _⊆_
    
    _⊆_
      : Collection R
      → Collection R
      → Set
    _⊆_
      = Subcollection
  
    ⊆-refl
      : (xs : Collection R)
      → xs ⊆ xs
    ⊆-refl (collection xs _)
      = List.⊆-refl xs
  
    ⊆-trans
      : (xs₁ xs₂ xs₃ : Collection R)
      → xs₁ ⊆ xs₂
      → xs₂ ⊆ xs₃
      → xs₁ ⊆ xs₃
    ⊆-trans (collection xs₁ _) (collection xs₂ _) (collection xs₃ _)
      = List.⊆-trans xs₁ xs₂ xs₃
  
    ⊆-empty
      : (xs : Collection R)
      → empty ⊆ xs
    ⊆-empty (collection xs _)
      = List.⊆-nil xs

    ⊆-insert
      : (xs : Collection R)
      → (s : Symmetric R)
      → (d : Decidable R)
      → (x : A)
      → (p : find xs (Bool.from-decidable d x) ≡ nothing)
      → xs ⊆ insert xs s d x p
    ⊆-insert (collection xs _) _ _ x _
      = List.⊆-cons x xs

    ⊆-insert-left
      : {x : A}
      → (xs₁ xs₂ : Collection R)
      → (s : Symmetric R)
      → (d : Decidable R)
      → (p : find xs₁ (Bool.from-decidable d x) ≡ nothing)
      → IsMember xs₂ x
      → xs₁ ⊆ xs₂
      → insert xs₁ s d x p ⊆ xs₂
    ⊆-insert-left (collection xs₁ _) _ _ _ _
      = List.⊆-cons-left xs₁

    ⊆-find
      : {y : A}
      → (xs₁ xs₂ : Collection R)
      → (f : A → Bool)
      → Unique R f
      → xs₁ ⊆ xs₂
      → find xs₁ f ≡ just y
      → find xs₂ f ≡ just y
    ⊆-find xs₁ xs₂ f u p q₁
      = is-member-find-unique xs₂ f u
        (find-just xs₁ f q₁)
        (p (find-is-member xs₁ f q₁))

-- ## Exports

open Collection public
  using (_⊆_)

