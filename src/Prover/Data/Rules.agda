module Prover.Data.Rules where

open import Prover.Data.Identifier
  using (Identifier; _≟_idn)
open import Prover.Data.Rule
  using (Rule; _≟_rul; rule)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Prelude

-- ## Utilities

relation
  : (ss : Symbols)
  → Relation (Rule ss)
relation _
  = Relation.map Rule.name
    (Equal Identifier)

symmetric
  : (ss : Symbols)
  → Symmetric (relation ss)
symmetric _
  = Symmetric.map Rule.name
    (Equal Identifier)
    (Symmetric.equal Identifier)

transitive
  : (ss : Symbols)
  → Transitive (relation ss)
transitive _
  = Transitive.map Rule.name
    (Equal Identifier)
    (Transitive.equal Identifier)

decidable
  : (ss : Symbols)
  → Decidable (relation ss)
decidable _
  = Decidable.map Rule.name
    (Equal Identifier)
    _≟_idn

-- ## Definition

Rules
  : Symbols
  → Set
Rules ss
  = Collection
    {A = Rule ss}
    (relation ss)

-- ## Module

module Rules where

  open Collection public
    using (Member; empty; member)

  -- ### Interface

  module _
    {ss : Symbols}
    where

    lookup
      : Rules ss
      → Identifier
      → Maybe (Rule ss)
    lookup rs n
      = Collection.find rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name)

    insert
      : (rs : Rules ss)
      → (r : Rule ss)
      → lookup rs (Rule.name r) ≡ nothing
      → Rules ss
    insert rs r
      = Collection.insert rs
        (symmetric ss)
        (decidable ss) r

  -- ### Membership

  module _
    {ss : Symbols}
    where

    rul_∈_
      : Rule ss
      → Rules ss
      → Set
    rul r ∈ rs
      = Collection.IsMember rs r

    rul_∈?_
      : (r : Rule ss)
      → (rs : Rules ss)
      → Dec (rul r ∈ rs)
    rul r ∈? rs
      = Collection.is-member? rs _≟_rul r

    lookup-member
      : (rs : Rules ss)
      → Identifier
      → Maybe (Member rs)
    lookup-member rs n
      = Collection.find-member rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name)

    lookup-member-nothing
      : (rs : Rules ss)
      → (r : Rule ss)
      → lookup-member rs (Rule.name r) ≡ nothing
      → ¬ rul r ∈ rs
    lookup-member-nothing rs r@(rule n _ _ _)
      = Collection.find-member-nothing rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name) r
        (Bool.from-decidable-true _≟_idn n n refl)

    lookup-member-just
      : (rs : Rules ss)
      → (r : Rule ss)
      → {m : Member rs}
      → .(rul r ∈ rs)
      → lookup-member rs (Rule.name r) ≡ just m
      → r ≡ Member.value m
    lookup-member-just rs r@(rule n _ _ _) p q
      = Collection.find-member-just-equal rs
        (Bool.from-decidable _≟_idn n ∘ Rule.name)
        (Unique.decidable (symmetric ss) (transitive ss) (decidable ss) r)
        (Bool.from-decidable-true _≟_idn n n refl)
        (Dec.recompute (rul r ∈? rs) p) q

-- ## Exports

open Rules public
  using (rul_∈_)

