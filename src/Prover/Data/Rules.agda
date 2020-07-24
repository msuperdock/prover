module Prover.Data.Rules where

open import Prover.Data.Identifier
  using (Identifier; _≟_idn)
open import Prover.Data.Rule
  using (Rule; _≟_rul?)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Prelude

-- ## Definition

Rules
  : Symbols
  → Set
Rules ss
  = Collection {A = Any (Rule ss)} (Rule.name ∘ Any.value) _≟_idn

-- ## Module

module Rules where

  open Collection public
    using (empty; lookup)

  -- ### Interface

  insert
    : {ss : Symbols}
    → {a : ℕ}
    → (rs : Rules ss)
    → (r : Rule ss a)
    → lookup rs (Rule.name r) ≡ nothing
    → Rules ss
  insert rs
    = Collection.insert rs ∘ any

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
      = Collection.is-member? _≟_rul? rs (any r)

    record Member
      (rs : Rules ss)
      : Set
      where

      constructor

        member

      field

        {arity}
          : ℕ

        rule
          : Rule ss arity

        is-member
          : rul rule ∈ rs

    lookup-member
      : (rs : Rules ss)
      → Identifier
      → Maybe (Member rs)
    lookup-member rs n
      with Collection.lookup-member rs n
    ... | nothing
      = nothing
    ... | just (Collection.member (any r) p)
      = just (member r p)

    lookup-member-any
      : {rs : Rules ss}
      → {m : Member rs}
      → {a : ℕ}
      → (r : Rule ss a)
      → .(rul r ∈ rs)
      → lookup-member rs (Rule.name r) ≡ just m
      → Equal (Any (Rule ss)) (any r) (any (Member.rule m))
    lookup-member-any {rs = rs} r p _
      with Collection.lookup-member rs (Rule.name r)
      | inspect (Collection.lookup-member rs) (Rule.name r)
    ... | just _ | [ q ]
      with Collection.lookup-member-eq (any r) (recompute (rul r ∈? rs) p) q
    lookup-member-any _ _ refl | _ | _ | refl
      = refl

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
      → r ≅ Member.rule m
    lookup-member-eq r p q
      with lookup-member-any r p q
    ... | refl
      = refl

    lookup-member-nothing
      : (rs : Rules ss)
      → (n : Identifier)
      → lookup-member rs n ≡ nothing
      → lookup rs n ≡ nothing
    lookup-member-nothing rs n p
      with Collection.lookup-member rs n
      | inspect (Collection.lookup-member rs) n
    ... | nothing | [ q ]
      = Collection.lookup-member-nothing rs n q

-- ## Exports

open Rules public
  using (rul_∈_)

