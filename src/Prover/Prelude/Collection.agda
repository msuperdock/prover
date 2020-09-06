module Prover.Prelude.Collection where

open import Prover.Prelude.Bool
  using (Bool; F; T; Unique; true)
open import Prover.Prelude.Empty
  using (¬_; ⊥-elim)
open import Prover.Prelude.Equal
  using (Equal; _≡_; refl; rewrite₂; sub; sym; trans)
open import Prover.Prelude.Fin
  using (Fin; _≟_fin; suc; zero)
open import Prover.Prelude.Function
  using (_$_; _∘_)
open import Prover.Prelude.List
  using (List; Sublist)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Nat
  using (ℕ)
open import Prover.Prelude.Relation
  using (Dec; Decidable; Injective; Relation; Symmetric; no; yes)
open import Prover.Prelude.Sigma
  using (Σ; _,_)

open List
  using ([]; _∷_; _!_)

-- ## Definition

module _Collection where

  record Collection
    {A : Set}
    (R : Relation A)
    : Set
    where
    
    constructor

      collection

    field
    
      elements
        : List A
      
    size
      : ℕ
    size
      = List.length elements
  
    field
  
      .valid
        : (k₁ k₂ : Fin size)
        → R (elements ! k₁) (elements ! k₂)
        → k₁ ≡ k₂

    valid'
      : (k₁ k₂ : Fin size)
      → R (elements ! k₁) (elements ! k₂)
      → k₁ ≡ k₂
    valid' k₁ k₂ r
      = Dec.recompute (k₁ ≟ k₂ fin) (valid k₁ k₂ r)

Collection
  : {A : Set}
  → Relation A
  → Set
Collection
  = _Collection.Collection

open _Collection public
  using (collection)

-- ## Module

module Collection where

  open _Collection.Collection public

  -- ### Interface

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
    → (k : Fin (size xs))
    → F (f (elements xs ! k))
  find-nothing (collection xs _)
    = List.find-nothing xs

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
          (Bool.from-decidable-true d x (xs' ! k₂) r))
      ; (suc k₁) zero r
        → ⊥-elim (Bool.¬both
          (find-nothing xs (Bool.from-decidable d x) p k₁)
          (Bool.from-decidable-true d x (xs' ! k₁) (s (xs' ! k₁) x r)))
      ; (suc k₁) (suc k₂) r
        → sub suc (valid' xs k₁ k₂ r)
      }
    }

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
      ∘ r (xs' ! k₁) (xs' ! k₂)
      ∘ rewrite₂ S
        (sym (List.lookup-map f xs' k₁))
        (sym (List.lookup-map f xs' k₂))
    }

  -- ### Construction

  empty
    : {A : Set}
    → {R : Relation A}
    → Collection R
  empty
    = record
    { elements
      = []
    ; valid
      = λ ()
    }

  -- ### Conversion

  from-list'
    : {A : Set}
    → (R : Relation A)
    → Decidable R
    → (xs : List A)
    → Dec ((k₁ k₂ : Fin (List.length xs))
      → R (xs ! k₁) (xs ! k₂)
      → k₁ ≡ k₂)
  from-list' R d xs
    = Fin.dec (λ (k₁ : Fin (List.length xs))
      → (k₂ : Fin (List.length xs))
      → R (xs ! k₁) (xs ! k₂)
      → k₁ ≡ k₂)
    $ λ (k₁ : Fin (List.length xs))
      → Fin.dec (λ (k₂ : Fin (List.length xs))
      → R (xs ! k₁) (xs ! k₂)
      → k₁ ≡ k₂)
    $ λ k₂ → Dec.function
      (d (xs ! k₁) (xs ! k₂))
      (k₁ ≟ k₂ fin)

  from-list
    : {A : Set}
    → (R : Relation A)
    → Decidable R
    → List A
    → Maybe (Collection R)
  from-list R d xs
    with from-list' R d xs
  ... | no _
    = nothing
  ... | yes f
    = just (collection xs f)

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

    collection-eq
      : {xs₁ xs₂ : Collection R}
      → elements xs₁ ≡ elements xs₂
      → xs₁ ≡ xs₂
    collection-eq refl
      = refl

  -- ### Membership

  module _
    {A : Set}
    {R : Relation A}
    where

    open List public
      using (member)

    IsMember
      : Collection R
      → A
      → Set
    IsMember (collection xs _)
      = List.IsMember xs

    is-member?
      : (xs : Collection R)
      → Decidable (Equal A)
      → (x : A)
      → Dec (IsMember xs x)
    is-member? (collection xs _)
      = List.is-member? xs

    is-member-eq
      : {x₁ x₂ : A}
      → (xs : Collection R)
      → IsMember xs x₁
      → IsMember xs x₂
      → R x₁ x₂
      → x₁ ≡ x₂
    is-member-eq xs@(collection xs' _) (k₁ , p₁) (k₂ , p₂) r
      = trans (sym p₁)
      $ trans (sub (List.lookup xs') (valid' xs k₁ k₂ (rewrite₂ R p₁ p₂ r)))
      $ p₂

    Member
      : Collection R
      → Set
    Member (collection xs _)
      = List.Member xs

    module Member where

      open List.Member public

    find-member
      : (xs : Collection R)
      → (A → Bool)
      → Maybe (Member xs)
    find-member (collection xs _)
      = List.find-member xs

  -- ### Properties

  find-just
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → find xs f ≡ just y
    → IsMember xs y
  find-just (collection xs _)
    = List.find-just xs

  find-true
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → find xs f ≡ just y
    → T (f y)
  find-true (collection xs _)
    = List.find-true xs

  find-insert
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → (s : Symmetric R)
    → (d : Decidable R)
    → (x : A)
    → (p : find xs (Bool.from-decidable d x) ≡ nothing)
    → (f : A → Bool)
    → f x ≡ true
    → find (insert xs s d x p) f ≡ just x
  find-insert (collection xs _) _ _ x _
    = List.find-cons xs x

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

  member-find
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → T (f y)
    → IsMember xs y
    → z ∈ A × find xs f ≡ just z
  member-find (collection xs _)
    = List.member-find xs

  member-find-unique
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → Unique R f
    → T (f y)
    → IsMember xs y
    → find xs f ≡ just y
  member-find-unique {y = y} xs f u p m
    with member-find xs f p m
  ... | (z , q)
    = trans q
    $ sub just
    $ is-member-eq xs
      (find-just xs f q) m
      (u z y (find-true xs f q) p)

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

  find-member-just
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → {m : Member xs}
    → (f : A → Bool)
    → find-member xs f ≡ just m
    → find xs f ≡ just (Member.value m)
  find-member-just (collection xs _)
    = List.find-member-just xs

  find-member-just-eq
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
  find-member-just-eq xs f u p m q
    = Maybe.just-injective
    $ trans (sym (member-find-unique xs f u p m))
    $ find-member-just xs f q

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
      : (xs₁ xs₂ : Collection R)
      → (s : Symmetric R)
      → (d : Decidable R)
      → (x : A)
      → (p : find xs₁ (Bool.from-decidable d x) ≡ nothing)
      → IsMember xs₂ x
      → xs₁ ⊆ xs₂
      → insert xs₁ s d x p ⊆ xs₂
    ⊆-insert-left (collection xs₁ _) (collection xs₂ _) _ _ x _
      = List.⊆-cons-left xs₁ xs₂ x

    ⊆-find
      : {y : A}
      → (xs₁ xs₂ : Collection R)
      → (f : A → Bool)
      → Unique R f
      → xs₁ ⊆ xs₂
      → find xs₁ f ≡ just y
      → find xs₂ f ≡ just y
    ⊆-find {y = y} xs₁ xs₂ f u p q₁
      = member-find-unique xs₂ f u
        (find-true xs₁ f q₁)
        (p y (find-just xs₁ f q₁))

-- ## Exports

open Collection public
  using (collection-eq)

