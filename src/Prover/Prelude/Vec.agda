module Prover.Prelude.Vec where

open import Prover.Prelude.Any
  using (Any; any)
open import Prover.Prelude.Bool
  using (Bool; F; T; false; true)
open import Prover.Prelude.Empty
  using (¬_; ⊥-elim)
open import Prover.Prelude.Equal
  using (Equal; _≡_; refl; sym; trans)
open import Prover.Prelude.Fin
  using (Fin; zero; suc)
open import Prover.Prelude.Function
  using (_∘_; id)
open import Prover.Prelude.Inspect
  using ([_]; inspect)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Nat
  using (ℕ; zero; suc)
open import Prover.Prelude.Relation
  using (Dec; Decidable; no; yes)
open import Prover.Prelude.Retraction
  using (Retraction)
open import Prover.Prelude.Sigma
  using (Σ; _,_; π₂)

open import Agda.Builtin.List using () renaming
  ( List
    to List'
  ; []
    to nil'
  ; _∷_
    to cons'
  )

-- ## Definition

module _Vec where

  data Vec
    (A : Set)
    : ℕ
    → Set
    where

    nil
      : Vec A zero

    cons
      : A
      → (xs : Any (Vec A))
      → Vec A (suc (Any.index xs))

Vec
  : Set
  → ℕ
  → Set
Vec
  = _Vec.Vec

open _Vec.Vec public

-- ## Module

module Vec where

  open _Vec.Vec public

  -- ### Interface

  infixr 5 _∷_

  pattern []
    = nil
  pattern _∷_ x xs
    = cons x (any xs)

  init
    : {A : Set}
    → {n : ℕ}
    → Vec A (suc n)
    → Vec A n
  init (_ ∷ [])
    = []
  init (x ∷ xs@(_ ∷ _))
    = x ∷ init xs

  last
    : {A : Set}
    → {n : ℕ}
    → Vec A (suc n)
    → A
  last (x ∷ [])
    = x
  last (_ ∷ xs@(_ ∷ _))
    = last xs

  lookup
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → Fin n
    → A
  lookup (x ∷ _) zero
    = x
  lookup (_ ∷ xs) (suc k)
    = lookup xs k

  _!_
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → Fin n
    → A
  _!_
    = lookup

  update
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → Fin n
    → A
    → Vec A n
  update (_ ∷ xs) zero y
    = y ∷ xs
  update (x ∷ xs) (suc k) y
    = x ∷ update xs k y

  insert
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → Fin (suc n)
    → A
    → Vec A (suc n)
  insert xs zero y
    = y ∷ xs
  insert (x ∷ xs) (suc k) y
    = x ∷ insert xs k y

  delete
    : {A : Set}
    → {n : ℕ}
    → Vec A (suc n)
    → Fin (suc n)
    → Vec A n
  delete (_ ∷ xs) zero
    = xs
  delete (x ∷ xs@(_ ∷ _)) (suc k)
    = x ∷ delete xs k

  map
    : {A B : Set}
    → {n : ℕ}
    → (A → B)
    → Vec A n
    → Vec B n
  map _ []
    = []
  map f (x ∷ xs)
    = f x ∷ map f xs

  -- ### Construction

  module _
    {A : Set}
    where

    snoc
      : {n : ℕ}
      → Vec A n
      → A
      → Vec A (suc n)
    snoc [] y
      = y ∷ []
    snoc (x ∷ xs) y
      = x ∷ snoc xs y

  -- ### Conversion

  module _
    {A : Set}
    where

    to-builtin
      : {n : ℕ}
      → Vec A n
      → List' A
    to-builtin []
      = nil'
    to-builtin (x ∷ xs)
      = cons' x (to-builtin xs)

  -- ### Equality

  module _
    {A : Set}
    where

    decidable
      : {n : ℕ}
      → Decidable (Equal A)
      → Decidable (Equal (Vec A n))
    decidable _ [] []
      = yes refl
    decidable d (x₁ ∷ xs₁) (x₂ ∷ xs₂)
      with d x₁ x₂ | decidable d xs₁ xs₂
    ... | no ¬p | _
      = no (λ {refl → ¬p refl})
    ... | _ | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl | yes refl
      = yes refl

    cons-eq
      : {n : ℕ}
      → {x₁ x₂ : A}
      → {xs₁ xs₂ : Vec A n}
      → x₁ ≡ x₂
      → xs₁ ≡ xs₂
      → x₁ ∷ xs₁ ≡ x₂ ∷ xs₂
    cons-eq refl refl
      = refl

  -- ### Retraction

  module _
    {A B : Set}
    where

    module VecRetraction
      (F : Retraction A B)
      where
  
      to
        : {n : ℕ}
        → Vec A n
        → Vec B n
      to xs
        = map (Retraction.to F) xs
  
      from
        : {n : ℕ}
        → Vec B n
        → Vec A n
      from ys
        = map (Retraction.from F) ys
    
      to-from
        : {n : ℕ}
        → (ys : Vec B n)
        → to (from ys) ≡ ys
      to-from []
        = refl
      to-from (y ∷ ys)
        = cons-eq
          (Retraction.to-from F y)
          (to-from ys)

    retraction
      : Retraction A B
      → (n : ℕ)
      → Retraction (Vec A n) (Vec B n)
    retraction F _
      = record {VecRetraction F}

  -- ### Membership

  module _
    {A : Set}
    where

    IsMember
      : {n : ℕ}
      → Vec A n
      → A
      → Set
    IsMember {n = n} xs x
      = k ∈ Fin n
      × xs ! k ≡ x
  
    is-member?
      : {n : ℕ}
      → (xs : Vec A n)
      → Decidable (Equal A)
      → (y : A)
      → Dec (IsMember xs y)
    is-member? [] _ _
      = no (λ ())
    is-member? (x ∷ xs) d y
      with d x y | is-member? xs d y
    ... | no ¬p | no ¬m
      = no (λ
        { (zero , p)
          → ¬p p
        ; (suc k , m)
          → ¬m (k , m)
        })
    ... | yes p | _
      = yes (zero , p)
    ... | _ | yes (k , m)
      = yes (suc k , m)

    record Member
      {n : ℕ}
      (xs : Vec A n)
      : Set
      where

      constructor

        member

      field

        value
          : A

        valid
          : IsMember xs value

  -- ### Properties

  lookup-update
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (k : Fin n)
    → (y : A)
    → update xs k y ! k ≡ y
  lookup-update (_ ∷ _) zero _
    = refl
  lookup-update (_ ∷ xs) (suc k) y
    = lookup-update xs k y

  lookup-map
    : {A B : Set}
    → {n : ℕ}
    → (f : A → B)
    → (xs : Vec A n)
    → (k : Fin n)
    → map f xs ! k ≡ f (xs ! k)
  lookup-map _ (_ ∷ _) zero
    = refl
  lookup-map f (_ ∷ xs) (suc k)
    = lookup-map f xs k

  map-update
    : {A B : Set}
    → {n : ℕ}
    → (f : A → B)
    → (xs : Vec A n)
    → (k : Fin n)
    → (y : A)
    → f y ≡ f (xs ! k)
    → map f (update xs k y) ≡ map f xs
  map-update _ (_ ∷ _) zero _ p
    = cons-eq p refl
  map-update f (_ ∷ xs) (suc k) y p
    = cons-eq refl (map-update f xs k y p)

  snoc-init-last
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A (suc n))
    → snoc (init xs) (last xs) ≡ xs
  snoc-init-last (_ ∷ [])
    = refl
  snoc-init-last (_ ∷ xs@(_ ∷ _))
    = cons-eq refl (snoc-init-last xs)

  -- ### Subvector

  module _
    {A : Set}
    where

    Subvec
      : {n₁ n₂ : ℕ}
      → Vec A n₁
      → Vec A n₂
      → Set
    Subvec xs₁ xs₂
      = (x : A)
      → IsMember xs₁ x
      → IsMember xs₂ x

    infix 4 _⊆_
    
    _⊆_
      : {n₁ n₂ : ℕ}
      → Vec A n₁
      → Vec A n₂
      → Set
    _⊆_
      = Subvec
  
    ⊆-refl
      : {n : ℕ}
      → (xs : Vec A n)
      → xs ⊆ xs
    ⊆-refl _ _
      = id

    ⊆-trans
      : {n₁ n₂ n₃ : ℕ}
      → (xs₁ : Vec A n₁)
      → (xs₂ : Vec A n₂)
      → (xs₃ : Vec A n₃)
      → xs₁ ⊆ xs₂
      → xs₂ ⊆ xs₃
      → xs₁ ⊆ xs₃
    ⊆-trans _ _ _ p₁ p₂ x
      = p₂ x ∘ p₁ x

    ⊆-nil
      : {n : ℕ}
      → (xs : Vec A n)
      → [] ⊆ xs
    ⊆-nil _ _ ()

    ⊆-cons
      : {n : ℕ}
      → (x : A)
      → (xs : Vec A n)
      → xs ⊆ x ∷ xs
    ⊆-cons _ _ _ (k , p)
      = (suc k , p)

    ⊆-cons-left
      : {n₁ n₂ : ℕ}
      → (xs₁ : Vec A n₁)
      → (xs₂ : Vec A n₂)
      → (x : A)
      → IsMember xs₂ x
      → xs₁ ⊆ xs₂
      → x ∷ xs₁ ⊆ xs₂
    ⊆-cons-left _ _ _ m _ _ (zero , refl)
      = m
    ⊆-cons-left _ _ _ _ p x (suc k , q)
      = p x (k , q)

  -- ### Find

  find
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → (A → Bool)
    → Maybe A
  find [] _
    = nothing
  find (x ∷ xs) f
    with f x
  ... | false
    = find xs f
  ... | true
    = just x

  find-member
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (A → Bool)
    → Maybe (Member xs)
  find-member [] _
    = nothing
  find-member (x ∷ xs) f
    with f x | find-member xs f
  ... | false | nothing
    = nothing
  ... | false | just (member y (k , p))
    = just (member y (suc k , p))
  ... | true | _
    = just (member x (zero , refl))

  find-true
    : {A : Set}
    → {n : ℕ}
    → {y : A}
    → (xs : Vec A n)
    → (f : A → Bool)
    → find xs f ≡ just y
    → T (f y)
  find-true (x ∷ xs) f p
    with f x | inspect f x
  ... | false | _
    = find-true xs f p
  find-true _ _ refl | true | [ q ]
    = q

  member-find
    : {A : Set}
    → {n : ℕ}
    → {y : A}
    → (xs : Vec A n)
    → (f : A → Bool)
    → T (f y)
    → IsMember xs y
    → z ∈ A × find xs f ≡ just z
  member-find (x ∷ _) f _ _
    with f x | inspect f x
  member-find _ _ p (zero , refl) | false | [ r ]
    = ⊥-elim (Bool.¬both r p)
  member-find (x ∷ xs) f p (suc k , q) | false | _
    = member-find xs f p (k , q)
  ... | true | _
    = (x , refl)

  find-is-member
    : {A : Set}
    → {n : ℕ}
    → {y : A}
    → (xs : Vec A n)
    → (f : A → Bool)
    → find xs f ≡ just y
    → IsMember xs y
  find-is-member (x ∷ xs) f p
    with f x
  ... | false
    with find-is-member xs f p
  ... | (k , q)
    = (suc k , q)
  find-is-member _ _ refl | true
    = (zero , refl)

  find-¬is-member
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (f : A → Bool)
    → (x : A)
    → T (f x)
    → find xs f ≡ nothing
    → ¬ IsMember xs x
  find-¬is-member xs f _ p q m
    = Maybe.nothing≢just (trans (sym q) (π₂ (member-find xs f p m)))

  find-nothing
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (f : A → Bool)
    → find xs f ≡ nothing
    → (k : Fin n)
    → F (f (xs ! k))
  find-nothing (x ∷ _) f _ _
    with f x | inspect f x
  find-nothing _ _ _ zero | false | [ p ]
    = p
  find-nothing (x ∷ xs) f p (suc k) | false | _
    = find-nothing xs f p k

  find-member-nothing
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (f : A → Bool)
    → find-member xs f ≡ nothing
    → find xs f ≡ nothing
  find-member-nothing [] _ _
    = refl
  find-member-nothing (x ∷ xs) f p
    with f x
    | find-member xs f
    | inspect (find-member xs) f
  ... | false | nothing | [ q ]
    = find-member-nothing xs f q

  find-member-just
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → {m : Member xs}
    → (f : A → Bool)
    → find-member xs f ≡ just m
    → find xs f ≡ just (Member.value m)
  find-member-just (x ∷ xs) f _
    with f x
    | find-member xs f
    | inspect (find-member xs) f
  find-member-just (_ ∷ xs) f refl | false | just _ | [ p ]
    = find-member-just xs f p
  find-member-just _ _ refl | true | _  | _
    = refl

  find-cons
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (x : A)
    → (f : A → Bool)
    → f x ≡ true
    → find (x ∷ xs) f ≡ just x
  find-cons _ x f _
    with f x
  find-cons _ _ _ refl | _
    = refl

  find-map
    : {A B : Set}
    → {n : ℕ}
    → {y : A}
    → (f : A → B)
    → (xs : Vec A n)
    → (g : B → Bool)
    → find xs (g ∘ f) ≡ just y
    → find (map f xs) g ≡ just (f y)
  find-map f (x ∷ xs) g p
    with g (f x)
  ... | false
    = find-map f xs g p
  find-map _ _ _ refl | true
    = refl

-- ## Exports

open Vec public
  using (Subvec)

