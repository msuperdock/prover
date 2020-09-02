module Prover.Data.Rules where

open import Prover.Data.Identifier
  using (Identifier; _≟_idn)
open import Prover.Data.Rule
  using (Rule; _≟_rul?)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Prelude

-- ## Utilities

relation
  : (ss : Symbols)
  → Relation (Any (Rule ss))
relation _
  = Relation.map
    (Rule.name ∘ Any.value)
    (Equal Identifier)

symmetric
  : (ss : Symbols)
  → Symmetric (relation ss)
symmetric _
  = Symmetric.map
    (Rule.name ∘ Any.value)
    (Equal Identifier)
    (Symmetric.equal Identifier)

transitive
  : (ss : Symbols)
  → Transitive (relation ss)
transitive _
  = Transitive.map
    (Rule.name ∘ Any.value)
    (Equal Identifier)
    (Transitive.equal Identifier)

decidable
  : (ss : Symbols)
  → Decidable (relation ss)
decidable _
  = Decidable.map
    (Rule.name ∘ Any.value)
    (Equal Identifier)
    _≟_idn

-- ## Definition

Rules
  : Symbols
  → Set
Rules ss
  = Collection {A = Any (Rule ss)} (relation ss)

-- ## Module

module Rules where

  -- ### Interface

  module _
    {ss : Symbols}
    where

    lookup
      : Rules ss
      → Identifier
      → Maybe (Any (Rule ss))
    lookup rs n
      = Collection.find rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name ∘ Any.value)

    insert
      : {a : ℕ}
      → (rs : Rules ss)
      → (r : Rule ss a)
      → lookup rs (Rule.name r) ≡ nothing
      → Rules ss
    insert rs r
      = Collection.insert rs (symmetric ss) (decidable ss) (any r)

  -- ### Construction

  open Collection public
    using (empty)

  -- ### Membership

  module _
    {ss : Symbols}
    where

    rul_∈_
      : {a : ℕ}
      → Rule ss a
      → Rules ss
      → Set
    rul r ∈ rs
      = Collection.IsMember rs (any r)

    rul_∈?_
      : {a : ℕ}
      → (r : Rule ss a)
      → (rs : Rules ss)
      → Dec (rul r ∈ rs)
    rul r ∈? rs
      = Collection.is-member? rs _≟_rul? (any r)

    record Member
      (rs : Rules ss)
      : Set
      where

      constructor

        member

      field

        {arity}
          : ℕ

        value
          : Rule ss arity

        is-member
          : rul value ∈ rs

    lookup-member
      : (rs : Rules ss)
      → Identifier
      → Maybe (Member rs)
    lookup-member rs n
      with Collection.find-member rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name ∘ Any.value)
    ... | nothing
      = nothing
    ... | just (Collection.member (any r) p)
      = just (member r p)

    lookup-member-nothing
      : {a : ℕ}
      → (rs : Rules ss)
      → (r : Rule ss a)
      → lookup-member rs (Rule.name r) ≡ nothing
      → ¬ rul r ∈ rs
    lookup-member-nothing rs r@(Rule.rule n _ _ _) _
      with Collection.find-member rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name ∘ Any.value)
      | inspect (Collection.find-member rs)
        (Bool.from-decidable _≟_idn n ∘ Rule.name ∘ Any.value)
    ... | nothing | [ q ]
      = Collection.find-¬is-member rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name ∘ Any.value) (any r)
        (Bool.from-decidable-true _≟_idn n n refl)
      $ Collection.find-member-nothing rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name ∘ Any.value) q

    lookup-member-any
      : {rs : Rules ss}
      → {m : Member rs}
      → {a : ℕ}
      → (r : Rule ss a)
      → .(rul r ∈ rs)
      → lookup-member rs (Rule.name r) ≡ just m
      → Equal (Any (Rule ss)) (any r) (any (Member.value m))
    lookup-member-any {rs = rs} (Rule.rule n _ _ _) _ _
      with Collection.find-member rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name ∘ Any.value)
      | inspect (Collection.find-member rs)
        (Bool.from-decidable _≟_idn n ∘ Rule.name ∘ Any.value)
    lookup-member-any {rs = rs} r@(Rule.rule n _ _ _) p refl
      | just _ | [ q ]
      = Collection.member-find-unique' rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name ∘ Any.value)
        (Unique.decidable (symmetric ss) (transitive ss) (decidable ss) (any r))
        (Bool.from-decidable-true (decidable ss) (any r) (any r) refl)
        (Dec.recompute (rul r ∈? rs) p) q
  
    lookup-member-arity
      : {rs : Rules ss}
      → {m : Member rs}
      → {a : ℕ}
      → (r : Rule ss a)
      → .(rul r ∈ rs)
      → lookup-member rs (Rule.name r) ≡ just m
      → a ≡ Member.arity m
    lookup-member-arity r p q
      with lookup-member-any r p q
    ... | refl
      = refl
  
    lookup-member-eq
      : {rs : Rules ss}
      → {m : Member rs}
      → {a : ℕ}
      → (r : Rule ss a)
      → .(rul r ∈ rs)
      → lookup-member rs (Rule.name r) ≡ just m
      → r ≅ Member.value m
    lookup-member-eq r p q
      with lookup-member-any r p q
    ... | refl
      = refl

-- ## Exports

open Rules public
  using (rul_∈_)

