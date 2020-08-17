module Prover.Prelude.Map where

open import Prover.Prelude.Bool
  using (Bool; Unique)
open import Prover.Prelude.Collection
  using (Collection)
open import Prover.Prelude.Equal
  using (Equal; _≡_; refl; sub)
open import Prover.Prelude.Function
  using (_$_; _∘_; const; id)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Relation
  using (Decidable; Relation; Symmetric; yes)
open import Prover.Prelude.Sigma
  using (module Sigma; _×_; _,_; π₁; π₂)

open Collection
  using (_⊆_)

-- ## Utilities

relation
  : (K A : Set)
  → Relation (K × A)
relation K _
  = Relation.map π₁ (Equal K)

symmetric
  : (K A : Set)
  → Symmetric (relation K A)
symmetric K _
  = Symmetric.map π₁ (Equal K)
    (Symmetric.equal K)

decidable
  : (K A : Set)
  → Decidable (Equal K)
  → Decidable (relation K A)
decidable K _
  = Decidable.map π₁ (Equal K)

-- ## Definition

Map
  : Set
  → Set
  → Set
Map K A
  = Collection (relation K A)

-- ## Module

module Map where

  -- ### Interface

  module _
    {K : Set}
    where

    lookup
      : {A : Set}
      → Map K A
      → Decidable (Equal K)
      → K
      → Maybe A
    lookup xs d k
      = Maybe.map π₂
        (Collection.find xs (Bool.from-decidable d k ∘ π₁))

    lookup-nothing
      : {A : Set}
      → (xs : Map K A)
      → (d : Decidable (Equal K))
      → (k : K)
      → lookup xs d k ≡ nothing
      → Collection.find xs (Bool.from-decidable d k ∘ π₁) ≡ nothing
    lookup-nothing xs d k
      = Maybe.map-nothing π₂
        (Collection.find xs (Bool.from-decidable d k ∘ π₁))

    lookup-just
      : {A : Set}
      → {y : A}
      → (xs : Map K A)
      → (d : Decidable (Equal K))
      → (k : K)
      → lookup xs d k ≡ just y
      → Collection.find xs (Bool.from-decidable d k ∘ π₁) ≡ just (k , y)
    lookup-just xs d k p
      with Maybe.map-just π₂
        (Collection.find xs (Bool.from-decidable d k ∘ π₁)) p
    ... | ((l , _) , q , refl)
      with d k l | Collection.find-true xs (Bool.from-decidable d k ∘ π₁) q
    ... | yes refl | _
      = q

    insert
      : {A : Set}
      → (xs : Map K A)
      → (d : Decidable (Equal K))
      → (k : K)
      → A
      → lookup xs d k ≡ nothing
      → Map K A
    insert {A = A} xs d k x p
      = Collection.insert xs
        (symmetric K A)
        (decidable K A d)
        (k , x)
        (lookup-nothing xs d k p)

    map
      : {A B : Set}
      → (A → B)
      → Map K A
      → Map K B
    map {B = B} f
      = Collection.map
        (relation K B)
        (Sigma.map (const f))
        (λ _ _ → id)

  -- ### Construction

  module _
    {K A : Set}
    where

    empty
      : Map K A
    empty
      = Collection.empty

  -- ### Properties

  module _
    {K : Set}
    where

    lookup-insert
      : {A : Set}
      → (xs : Map K A)
      → (d : Decidable (Equal K))
      → (k : K)
      → (x : A)
      → (p : lookup xs d k ≡ nothing)
      → lookup (insert xs d k x p) d k ≡ just x
    lookup-insert {A = A} xs d k x p
      = sub (Maybe.map π₂)
      $ Collection.find-insert xs
        (symmetric K A)
        (decidable K A d)
        (k , x)
        (lookup-nothing xs d k p)
        (Bool.from-decidable d k ∘ π₁)
        (Bool.from-decidable-true d k k refl)

    lookup-map
      : {A B : Set}
      → {x : A}
      → (f : A → B)
      → (xs : Map K A)
      → (d : Decidable (Equal K))
      → (k : K)
      → lookup xs d k ≡ just x
      → lookup (map f xs) d k ≡ just (f x)
    lookup-map {B = B} f xs d k p
      = sub (Maybe.map π₂)
      $ Collection.find-map
        (relation K B)
        (Sigma.map (const f))
        (λ _ _ → id) xs
        (Bool.from-decidable d k ∘ π₁)
        (lookup-just xs d k p)

    lookup-is-member
      : {A : Set}
      → {x : A}
      → (xs : Map K A)
      → (d : Decidable (Equal K))
      → (k : K)
      → lookup xs d k ≡ just x
      → Collection.IsMember xs (k , x)
    lookup-is-member xs d k p
      = Collection.find-is-member xs
        (Bool.from-decidable d k ∘ π₁)
        (lookup-just xs d k p)

  -- ### Submap

  module _
    {K A : Set}
    where

    ⊆-refl
      : (xs : Map K A)
      → xs ⊆ xs
    ⊆-refl
      = Collection.⊆-refl

    ⊆-trans
      : (xs₁ xs₂ xs₃ : Map K A)
      → xs₁ ⊆ xs₂
      → xs₂ ⊆ xs₃
      → xs₁ ⊆ xs₃
    ⊆-trans
      = Collection.⊆-trans

    ⊆-lookup
      : {y : A}
      → (xs₁ xs₂ : Map K A)
      → (d : Decidable (Equal K))
      → (k : K)
      → xs₁ ⊆ xs₂
      → lookup xs₁ d k ≡ just y
      → lookup xs₂ d k ≡ just y
    ⊆-lookup xs₁ xs₂ d k p q
      = sub (Maybe.map π₂)
      $ Collection.⊆-find xs₁ xs₂
        (Bool.from-decidable d k ∘ π₁)
        (Unique.map π₁ (Equal K) (Bool.from-decidable d k)
          (Unique.equal d k)) p
        (lookup-just xs₁ d k q)

    ⊆-empty
      : (xs : Map K A)
      → empty ⊆ xs
    ⊆-empty
      = Collection.⊆-empty

    ⊆-insert
      : (xs : Map K A)
      → (d : Decidable (Equal K))
      → (k : K)
      → (x : A)
      → (p : lookup xs d k ≡ nothing)
      → xs ⊆ insert xs d k x p
    ⊆-insert xs d k x p
      = Collection.⊆-insert xs
        (symmetric K A)
        (decidable K A d)
        (k , x)
        (lookup-nothing xs d k p)

    ⊆-insert-left
      : (xs₁ xs₂ : Map K A)
      → (d : Decidable (Equal K))
      → (k : K)
      → (x : A)
      → (p : lookup xs₁ d k ≡ nothing)
      → lookup xs₂ d k ≡ just x
      → xs₁ ⊆ xs₂
      → insert xs₁ d k x p ⊆ xs₂
    ⊆-insert-left xs₁ xs₂ d k x p q r
      = Collection.⊆-insert-left xs₁ xs₂
        (symmetric K A)
        (decidable K A d)
        (k , x)
        (lookup-nothing xs₁ d k p)
        (lookup-is-member xs₂ d k q) r

