module Prover.Data.Vec where

open import Prover.Data.Bool
  using (Bool; F; T; false; true)
open import Prover.Data.Empty
  using (¬_; ⊥-elim)
open import Prover.Data.Equal
  using (Equal; _≡_; refl)
open import Prover.Data.Fin
  using (Fin; suc; zero)
open import Prover.Data.Function
  using (_∘_; id)
open import Prover.Data.Inspect
  using ([_]; inspect)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Nat
  using (ℕ; suc)
open import Prover.Data.Relation
  using (Dec; Decidable; no; yes)
open import Prover.Data.Sigma
  using (Σ; _,_)

import Data.Vec
  as Vec'

-- ## Definition

Vec
  = Vec'.Vec

-- ## Module

module Vec where

  open Vec'.Vec public

  -- ### Interface

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

  snoc-init-last
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A (suc n))
    → snoc (init xs) (last xs) ≡ xs
  snoc-init-last (_ ∷ [])
    = refl
  snoc-init-last (_ ∷ xs@(_ ∷ _))
    = cons-equal refl (snoc-init-last xs)

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

  find-nothing
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (f : A → Bool)
    → find xs f ≡ nothing
    → (k : Fin n)
    → F (f (xs ! k))
  find-nothing (x ∷ _) f _ _
    with f x
    | inspect f x
  find-nothing _ _ _ zero | false | [ p ]
    = p
  find-nothing (x ∷ xs) f p (suc k) | false | _
    = find-nothing xs f p k

  find-just
    : {A : Set}
    → {n : ℕ}
    → {y : A}
    → (xs : Vec A n)
    → (f : A → Bool)
    → find xs f ≡ just y
    → T (f y)
  find-just (x ∷ xs) f p
    with f x
    | inspect f x
  ... | false | _
    = find-just xs f p
  find-just _ _ refl | true | [ q ]
    = q

  find-cons
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (x : A)
    → (f : A → Bool)
    → T (f x)
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
    = cons-equal p refl
  map-update f (_ ∷ xs) (suc k) y p
    = cons-equal refl (map-update f xs k y p)

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
      with d x₁ x₂
      | decidable d xs₁ xs₂
    ... | no ¬p | _
      = no (λ {refl → ¬p refl})
    ... | _ | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl | yes refl
      = yes refl

  -- ### Membership

  module _
    {A : Set}
    where

    record IsMember
      {n : ℕ}
      (xs : Vec A n)
      (x : A)
      : Set
      where

      constructor

        is-member

      field

        index
          : Fin n

        valid
          : xs ! index ≡ x
    
    is-member?
      : {n : ℕ}
      → (xs : Vec A n)
      → Decidable (Equal A)
      → (y : A)
      → Dec (IsMember xs y)
    is-member? [] _ _
      = no (λ ())
    is-member? (x ∷ xs) d y
      with d x y
      | is-member? xs d y
    ... | no ¬p | no ¬m
      = no (λ
        { (is-member zero p)
          → ¬p p
        ; (is-member (suc k) m)
          → ¬m (is-member k m)
        })
    ... | yes p | _
      = yes (is-member zero p)
    ... | _ | yes (is-member k m)
      = yes (is-member (suc k) m)

    is-member-cons
      : {n : ℕ}
      → {xs : Vec A n}
      → {y : A}
      → (x : A)
      → IsMember xs y
      → IsMember (x ∷ xs) y
    is-member-cons _ (is-member k p)
      = is-member (suc k) p

    find-is-member
      : {n : ℕ}
      → {y : A}
      → (xs : Vec A n)
      → (f : A → Bool)
      → find xs f ≡ just y
      → IsMember xs y
    find-is-member (x ∷ xs) f p
      with f x
    ... | false
      with find-is-member xs f p
    ... | is-member k q
      = is-member (suc k) q
    find-is-member _ _ refl | true
      = is-member zero refl

    is-member-find
      : {n : ℕ}
      → {y : A}
      → (xs : Vec A n)
      → (f : A → Bool)
      → T (f y)
      → IsMember xs y
      → z ∈ A × find xs f ≡ just z
    is-member-find (x ∷ _) f _ _
      with f x
      | inspect f x
    is-member-find _ _ p (is-member zero refl) | false | [ r ]
      = ⊥-elim (Bool.¬both r p)
    is-member-find (x ∷ xs) f p (is-member (suc k) q) | false | _
      = is-member-find xs f p (is-member k q)
    ... | true | _
      = (x , refl)

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

    find-member
      : {n : ℕ}
      → (xs : Vec A n)
      → (A → Bool)
      → Maybe (Member xs)
    find-member [] _
      = nothing
    find-member (x ∷ xs) f
      with f x
      | find-member xs f
    ... | false | nothing
      = nothing
    ... | false | just (member y p)
      = just (member y (is-member-cons x p))
    ... | true | _
      = just (member x (is-member zero refl))

    find-member-nothing
      : {n : ℕ}
      → (xs : Vec A n)
      → (f : A → Bool)
      → (x : A)
      → T (f x)
      → find-member xs f ≡ nothing
      → ¬ IsMember xs x
    find-member-nothing (x ∷ xs) f _ _ _ _
      with f x
      | inspect f x
      | find-member xs f
      | inspect (find-member xs) f
    find-member-nothing _ _ _ p _ (is-member zero refl)
      | false | [ q ] | _ | _
      = Bool.¬both q p
    find-member-nothing (_ ∷ xs) f x p _ (is-member (suc k) q)
      | _ | _ | nothing | [ r ]
      = find-member-nothing xs f x p r (is-member k q)

    find-member-just
      : {n : ℕ}
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
      = {x : A}
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
    ⊆-refl _
      = id

    ⊆-trans
      : {n₁ n₂ n₃ : ℕ}
      → (xs₁ : Vec A n₁)
      → (xs₂ : Vec A n₂)
      → (xs₃ : Vec A n₃)
      → xs₁ ⊆ xs₂
      → xs₂ ⊆ xs₃
      → xs₁ ⊆ xs₃
    ⊆-trans _ _ _ p₁ p₂
      = p₂ ∘ p₁

    ⊆-nil
      : {n : ℕ}
      → (xs : Vec A n)
      → [] ⊆ xs
    ⊆-nil _ ()

    ⊆-cons
      : {n : ℕ}
      → (x : A)
      → (xs : Vec A n)
      → xs ⊆ x ∷ xs
    ⊆-cons x _
      = is-member-cons x

    ⊆-cons-left
      : {n₁ n₂ : ℕ}
      → {xs₂ : Vec A n₂}
      → {x : A}
      → (xs₁ : Vec A n₁)
      → IsMember xs₂ x
      → xs₁ ⊆ xs₂
      → x ∷ xs₁ ⊆ xs₂
    ⊆-cons-left _ m _ (is-member zero refl)
      = m
    ⊆-cons-left _ _ p (is-member (suc k) q)
      = p (is-member k q)

-- ## Exports

open Vec public
  using (Subvec; []; _∷_; _!_; cons; nil)

