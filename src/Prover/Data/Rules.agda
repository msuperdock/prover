module Prover.Data.Rules where

open import Prover.Data.Collection.Named
  using (NamedCollection)
open import Prover.Data.Empty
  using (¬_)
open import Prover.Data.Equal
  using (_≡_)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Rule
  using (Rule; _≟_rul)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text
  using (Text)

-- ## Definition

Rules
  : Symbols
  → Set
Rules ss
  = NamedCollection (Rule.name {ss = ss})

-- ## Module

module Rules where

  open NamedCollection public
    using (member)

  -- ### Interface

  module _
    {ss : Symbols}
    where

    lookup
      : Rules ss
      → Text
      → Maybe (Rule ss)
    lookup
      = NamedCollection.lookup Rule.name

    insert
      : (rs : Rules ss)
      → (r : Rule ss)
      → lookup rs (Rule.name r) ≡ nothing
      → Rules ss
    insert
      = NamedCollection.insert Rule.name

  -- ### Construction

  module _
    {ss : Symbols}
    where

    empty
      : Rules ss
    empty
      = NamedCollection.empty Rule.name

  -- ### Membership

  module _
    {ss : Symbols}
    where

    rul_∈_
      : Rule ss
      → Rules ss
      → Set
    rul r ∈ rs
      = NamedCollection.IsMember Rule.name rs r

    Member
      : Rules ss
      → Set
    Member
      = NamedCollection.Member Rule.name

    module Member where

      open NamedCollection.Member public

    lookup-member
      : (rs : Rules ss)
      → Text
      → Maybe (Member rs)
    lookup-member
      = NamedCollection.lookup-member Rule.name

    lookup-member-nothing
      : (rs : Rules ss)
      → (r : Rule ss)
      → lookup-member rs (Rule.name r) ≡ nothing
      → ¬ rul r ∈ rs
    lookup-member-nothing
      = NamedCollection.lookup-member-nothing Rule.name

    lookup-member-just
      : (rs : Rules ss)
      → (r : Rule ss)
      → {m : Member rs}
      → .(rul r ∈ rs)
      → lookup-member rs (Rule.name r) ≡ just m
      → r ≡ Member.value m
    lookup-member-just rs
      = NamedCollection.lookup-member-just Rule.name rs _≟_rul

-- ## Exports

open Rules public
  using (rul_∈_)

