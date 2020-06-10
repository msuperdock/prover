module Prover.Prelude.Vec where

open import Prover.Prelude.Decidable
  using (Dec; Decidable; no; yes)
open import Prover.Prelude.Equality
  using (Equal; _≡_; refl; sub)
open import Prover.Prelude.Fin
  using (Fin; zero; suc)
open import Prover.Prelude.Nat
  using (Nat; ℕ; _+_; zero; suc)
open import Prover.Prelude.Retraction
  using (Retraction)

-- ## Definition

module _Vec where

  infixr 5 _∷_

  data Vec
    (A : Set)
    : ℕ
    → Set
    where

    []
      : Vec A zero

    _∷_
      : {n : ℕ}
      → A
      → Vec A n
      → Vec A (suc n)

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

  module _
    {A : Set}
    where

    init
      : {n : ℕ}
      → Vec A (suc n)
      → Vec A n
    init (_ ∷ [])
      = []
    init (x ∷ xs@(_ ∷ _))
      = x ∷ init xs

    last
      : {n : ℕ}
      → Vec A (suc n)
      → A
    last (x ∷ [])
      = x
    last (_ ∷ xs@(_ ∷ _))
      = last xs

    _!_
      : {n : ℕ}
      → Vec A n
      → Fin n
      → A
    (x ∷ _) ! zero
      = x
    (_ ∷ xs) ! (suc k)
      = xs ! k
  
    update
      : {n : ℕ}
      → Vec A n
      → Fin n
      → A
      → Vec A n
    update (_ ∷ xs) zero y
      = y ∷ xs
    update (x ∷ xs) (suc k) y
      = x ∷ update xs k y
  
    insert
      : {n : ℕ}
      → Vec A n
      → Fin (suc n)
      → A
      → Vec A (suc n)
    insert xs zero y
      = y ∷ xs
    insert (x ∷ xs) (suc k) y
      = x ∷ insert xs k y
  
    delete
      : {n : ℕ}
      → Vec A (suc n)
      → Fin (suc n)
      → Vec A n
    delete (_ ∷ xs) zero
      = xs
    delete (x ∷ xs@(_ ∷ _)) (suc k)
      = x ∷ delete xs k
  
    map
      : {B : Set}
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

  -- ### Equality

  module _
    {A : Set}
    where

    cons-eq
      : {n : ℕ}
      → {x₁ x₂ : A}
      → {xs₁ xs₂ : Vec A n}
      → x₁ ≡ x₂
      → xs₁ ≡ xs₂
      → x₁ ∷ xs₁ ≡ x₂ ∷ xs₂
    cons-eq refl refl
      = refl

    decidable
      : {n : ℕ}
      → Decidable A
      → Decidable (Vec A n)
    decidable _ [] []
      = yes refl
    decidable p (x₁ ∷ xs₁) (x₂ ∷ xs₂)
      with p x₁ x₂ | decidable p xs₁ xs₂
    ... | no ¬q | _
      = no (λ {refl → ¬q refl})
    ... | _ | no ¬q
      = no (λ {refl → ¬q refl})
    ... | yes refl | yes refl
      = yes refl

  -- ### Retraction

  module _
    {A B : Set}
    where

    module VecRetraction
      (r : Retraction A B)
      where
  
      to
        : {n : ℕ}
        → Vec A n
        → Vec B n
      to xs
        = map (Retraction.to r) xs
  
      from
        : {n : ℕ}
        → Vec B n
        → Vec A n
      from ys
        = map (Retraction.from r) ys
    
      to-from
        : {n : ℕ}
        → (ys : Vec B n)
        → to (from ys) ≡ ys
      to-from []
        = refl
      to-from (y ∷ ys)
        = cons-eq
          (Retraction.to-from r y)
          (to-from ys)

    retraction
      : Retraction A B
      → (n : ℕ)
      → Retraction (Vec A n) (Vec B n)
    retraction r _
      = record {VecRetraction r}

  -- ### Properties

  module _
    {A : Set}
    where

    ∷-injective-head
      : {n : ℕ}
      → {x y : A}
      → {xs ys : Vec A n}
      → Equal (Vec A (suc n)) (Vec A (suc n)) (x ∷ xs) (y ∷ ys)
      → x ≡ y
    ∷-injective-head refl
      = refl
  
    ∷-injective-tail
      : {n : ℕ}
      → {x y : A}
      → {xs ys : Vec A n}
      → Equal (Vec A (suc n)) (Vec A (suc n)) (x ∷ xs) (y ∷ ys)
      → xs ≡ ys
    ∷-injective-tail refl
      = refl
  
    snoc-init-last
      : {n : ℕ}
      → (xs : Vec A (suc n))
      → snoc (init xs) (last xs) ≡ xs
    snoc-init-last (_ ∷ [])
      = refl
    snoc-init-last (x ∷ xs@(_ ∷ _))
      = cons-eq refl (snoc-init-last xs)

    lookup-update
      : {n : ℕ}
      → (xs : Vec A n)
      → (k : Fin n)
      → (x : A)
      → update xs k x ! k ≡ x
    lookup-update (_ ∷ _) zero _
      = refl
    lookup-update (_ ∷ xs) (suc k) x
      = lookup-update xs k x
  
    map-update
      : {B : Set}
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

    data IsMember
      : {n : ℕ}
      → Vec A n
      → A
      → Set
      where
  
      head
        : {n : ℕ}
        → {x y : A}
        → {xs : Vec A n}
        → y ≡ x
        → IsMember (x ∷ xs) y
  
      tail
        : {n : ℕ}
        → {x y : A}
        → {xs : Vec A n}
        → IsMember xs y
        → IsMember (x ∷ xs) y
  
    is-member?
      : {n : ℕ}
      → Decidable A
      → (xs : Vec A n)
      → (y : A)
      → Dec (IsMember xs y)
    is-member? _ [] y
      = no (λ ())
    is-member? p (x ∷ xs) y
      with p y x | is-member? p xs y
    ... | no ¬q | no ¬m
      = no (λ {(head r) → ¬q r; (tail r) → ¬m r})
    ... | yes q | _
      = yes (head q)
    ... | _ | yes m
      = yes (tail m)

-- ## Exports

open Vec public
  using (_!_)

