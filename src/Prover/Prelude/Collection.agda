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
  find xs
    = List.find
      (elements xs)

  find-nothing
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → (f : A → Bool)
    → find xs f ≡ nothing
    → (k : Fin (size xs))
    → F (f (elements xs ! k))
  find-nothing xs
    = List.find-nothing
      (elements xs)

  insert
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → Symmetric R
    → (d : Decidable R)
    → (x : A)
    → find xs (Bool.from-decidable d x) ≡ nothing
    → Collection R
  insert xs s d x p
    = record
    { elements
      = x ∷ elements xs
    ; valid
      = λ
      { zero zero _
        → refl
      ; zero (suc k₂) r
        → ⊥-elim (Bool.¬both
          (find-nothing xs (Bool.from-decidable d x) p k₂)
          (Bool.from-decidable-true d x (elements xs ! k₂) r))
      ; (suc k₁) zero r
        → ⊥-elim (Bool.¬both
          (find-nothing xs (Bool.from-decidable d x) p k₁)
          (Bool.from-decidable-true d x (elements xs ! k₁)
            (s (elements xs ! k₁) x r)))
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
  map S f r xs
    = record
    { elements
      = List.map f
        (elements xs)
    ; valid
      = λ k₁ k₂
      → valid' xs k₁ k₂
      ∘ r (elements xs ! k₁) (elements xs ! k₂)
      ∘ rewrite₂ S
        (sym (List.lookup-map f (elements xs) k₁))
        (sym (List.lookup-map f (elements xs) k₂))
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
    decidable d xs₁ xs₂
      with List.decidable d (elements xs₁) (elements xs₂)
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
    IsMember xs
      = List.IsMember
        (elements xs)

    is-member?
      : (xs : Collection R)
      → Decidable (Equal A)
      → (x : A)
      → Dec (IsMember xs x)
    is-member? xs
      = List.is-member? (elements xs)

    is-member-eq
      : {x₁ x₂ : A}
      → (xs : Collection R)
      → IsMember xs x₁
      → IsMember xs x₂
      → R x₁ x₂
      → x₁ ≡ x₂
    is-member-eq xs (k₁ , p₁) (k₂ , p₂) r
      = trans
        (sym p₁)
      $ trans
        (sub (List.lookup (elements xs))
          (valid' xs k₁ k₂
            (rewrite₂ R p₁ p₂ r)))
      $ p₂

    Member
      : Collection R
      → Set
    Member xs
      = List.Member
        (elements xs)

    module Member where

      open List.Member public

    find-member
      : (xs : Collection R)
      → (A → Bool)
      → Maybe (Member xs)
    find-member xs
      = List.find-member
        (elements xs)

  -- ### Properties

  find-true
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → find xs f ≡ just y
    → T (f y)
  find-true xs
    = List.find-true
      (elements xs)

  find-is-member
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → find xs f ≡ just y
    → IsMember xs y
  find-is-member xs
    = List.find-is-member
      (elements xs)

  find-¬is-member
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → (f : A → Bool)
    → (x : A)
    → T (f x)
    → find xs f ≡ nothing
    → ¬ IsMember xs x
  find-¬is-member xs
    = List.find-¬is-member
      (elements xs)

  find-member-nothing
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → (f : A → Bool)
    → find-member xs f ≡ nothing
    → find xs f ≡ nothing
  find-member-nothing xs
    = List.find-member-nothing
      (elements xs)

  find-member-just
    : {A : Set}
    → {R : Relation A}
    → (xs : Collection R)
    → {m : Member xs}
    → (f : A → Bool)
    → find-member xs f ≡ just m
    → find xs f ≡ just (Member.value m)
  find-member-just xs
    = List.find-member-just
      (elements xs)

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
  find-insert xs _ _ x _
    = List.find-cons
      (elements xs) x

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
  find-map _ f _ xs
    = List.find-map f
      (elements xs)

  member-find
    : {A : Set}
    → {R : Relation A}
    → {y : A}
    → (xs : Collection R)
    → (f : A → Bool)
    → T (f y)
    → IsMember xs y
    → z ∈ A × find xs f ≡ just z
  member-find xs
    = List.member-find
      (elements xs)

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
      (find-is-member xs f q) m
      (u z y (find-true xs f q) p)

  member-find-unique'
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
  member-find-unique' xs f u p m q
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
    Subcollection xs₁ xs₂
      = Sublist
        (elements xs₁)
        (elements xs₂)
    
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
    ⊆-refl xs
      = List.⊆-refl
        (elements xs)
  
    ⊆-trans
      : (xs₁ xs₂ xs₃ : Collection R)
      → xs₁ ⊆ xs₂
      → xs₂ ⊆ xs₃
      → xs₁ ⊆ xs₃
    ⊆-trans xs₁ xs₂ xs₃
      = List.⊆-trans
        (elements xs₁)
        (elements xs₂)
        (elements xs₃)
  
    ⊆-empty
      : (xs : Collection R)
      → empty ⊆ xs
    ⊆-empty xs
      = List.⊆-nil
        (elements xs)

    ⊆-insert
      : (xs : Collection R)
      → (s : Symmetric R)
      → (d : Decidable R)
      → (x : A)
      → (p : find xs (Bool.from-decidable d x) ≡ nothing)
      → xs ⊆ insert xs s d x p
    ⊆-insert xs _ _ x _
      = List.⊆-cons x
        (elements xs)

    ⊆-insert-left
      : (xs₁ xs₂ : Collection R)
      → (s : Symmetric R)
      → (d : Decidable R)
      → (x : A)
      → (p : find xs₁ (Bool.from-decidable d x) ≡ nothing)
      → IsMember xs₂ x
      → xs₁ ⊆ xs₂
      → insert xs₁ s d x p ⊆ xs₂
    ⊆-insert-left xs₁ xs₂ _ _ x _
      = List.⊆-cons-left
        (elements xs₁)
        (elements xs₂) x

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
        (p y (find-is-member xs₁ f q₁))

-- ## Exports

open Collection public
  using (collection-eq)

