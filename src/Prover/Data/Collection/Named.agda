module Prover.Data.Collection.Named where

open import Prover.Data.Bool
  using (Bool; Unique)
open import Prover.Data.Collection
  using (Collection)
open import Prover.Data.Empty
  using (¬_)
open import Prover.Data.Equal
  using (Equal; _≡_; refl)
open import Prover.Data.Function
  using (_$_; _∘_)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Relation
  using (Dec; Decidable; Relation; Symmetric; Transitive)
open import Prover.Data.Text
  using (Text; _≟_txt)

-- ## Utilities

module _
  {A : Set}
  where

  relation
    : (A → Text)
    → Relation A
  relation f
    = Relation.map f (Equal Text)

  symmetric
    : (f : A → Text)
    → Symmetric (relation f)
  symmetric f
    = Symmetric.map f (Equal Text)
    $ Symmetric.equal Text

  transitive
    : (f : A → Text)
    → Transitive (relation f)
  transitive f
    = Transitive.map f (Equal Text)
    $ Transitive.equal Text

  decidable'
    : (f : A → Text)
    → Decidable (relation f)
  decidable' f
    = Decidable.map f (Equal Text)
    $ _≟_txt

-- ## Definition

NamedCollection
  : {A : Set}
  → (A → Text)
  → Set
NamedCollection f
  = Collection (relation f)

-- ## Module

module NamedCollection
  {A : Set}
  (f : A → Text)
  where

  open Collection public
    using (member)

  -- ### Interface

  lookup
    : NamedCollection f
    → Text
    → Maybe A
  lookup ss n
    = Collection.find ss
      (Bool.from-decidable _≟_txt n ∘ f)

  insert
    : (xs : NamedCollection f)
    → (x : A)
    → lookup xs (f x) ≡ nothing
    → NamedCollection f
  insert xs x
    = Collection.insert xs
      (symmetric f)
      (decidable' f) x

  -- ### Equality

  decidable
    : Decidable (Equal A)
    → Decidable (Equal (NamedCollection f))
  decidable
    = Collection.decidable

  -- ### Construction

  empty
    : NamedCollection f
  empty
    = Collection.empty

  -- ### Membership

  IsMember
    : NamedCollection f
    → A
    → Set
  IsMember
    = Collection.IsMember

  is-member?
    : (xs : NamedCollection f)
    → Decidable (Equal A)
    → (x : A)
    → Dec (IsMember xs x)
  is-member?
    = Collection.is-member?

  Member
    : NamedCollection f
    → Set
  Member
    = Collection.Member

  module Member where
  
    open Collection.Member public

  lookup-member
    : (xs : NamedCollection f)
    → Text
    → Maybe (Member xs)
  lookup-member xs n
    = Collection.find-member xs
      (Bool.from-decidable _≟_txt n ∘ f)

  lookup-member-nothing
    : (xs : NamedCollection f)
    → (x : A)
    → lookup-member xs (f x) ≡ nothing
    → ¬ IsMember xs x
  lookup-member-nothing xs x
    = Collection.find-member-nothing xs
      (Bool.from-decidable _≟_txt (f x) ∘ f) x
      (Bool.from-decidable-true _≟_txt (f x) (f x) refl)

  lookup-member-just
    : (xs : NamedCollection f)
    → Decidable (Equal A)
    → (x : A)
    → {m : Member xs}
    → .(IsMember xs x)
    → lookup-member xs (f x) ≡ just m
    → x ≡ Member.value m
  lookup-member-just xs p x q
    = Collection.find-member-just xs
      (Bool.from-decidable _≟_txt (f x) ∘ f)
      (Unique.decidable (symmetric f) (transitive f) (decidable' f) x)
      (Bool.from-decidable-true _≟_txt (f x) (f x) refl)
      (Dec.recompute (is-member? xs p x) q)

