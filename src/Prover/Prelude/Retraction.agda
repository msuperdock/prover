module Prover.Prelude.Retraction where

open import Prover.Prelude.Equality
  using (_≡_; refl; sub)
open import Prover.Prelude.Function
  using (_∘_; id)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Sigma
  using (_×_; _,_)

-- ## Retraction

-- ### Definition

record Retraction
  (A B : Set)
  : Set
  where

  field

    to
      : A
      → B

    from
      : B
      → A

    to-from
      : (y : B)
      → to (from y) ≡ y

-- ### Identity

module RetractionIdentity
  (A : Set)
  where

  to
    : A
    → A
  to
    = id

  from
    : A
    → A
  from
    = id

  to-from
    : (y : A)
    → to (from y) ≡ y
  to-from _
    = refl

retraction-identity
  : (A : Set)
  → Retraction A A
retraction-identity A
  = record {RetractionIdentity A}

-- ### Compose

module _
  {A B C : Set}
  where

  module RetractionCompose
    (F : Retraction B C)
    (G : Retraction A B)
    where

    to
      : A
      → C
    to
      = Retraction.to F
      ∘ Retraction.to G
  
    from
      : C
      → A
    from
      = Retraction.from G
      ∘ Retraction.from F
  
    to-from
      : (z : C)
      → to (from z) ≡ z
    to-from z
      with Retraction.to G (Retraction.from G (Retraction.from F z))
      | Retraction.to-from G (Retraction.from F z)
    ... | _ | refl
      = Retraction.to-from F z

  retraction-compose
    : Retraction B C
    → Retraction A B
    → Retraction A C
  retraction-compose F G
    = record {RetractionCompose F G}

-- ## PartialRetraction

-- ### Definition

record PartialRetraction
  (A B : Set)
  : Set
  where

  field

    to
      : A
      → Maybe B

    from
      : B
      → A

    to-from
      : (y : B)
      → to (from y) ≡ just y

-- ### Conversion

  -- partial-retraction
  --   : PartialRetraction A B
  -- partial-retraction
  --   = record
  --   { to
  --     = just ∘ to
  --   ; from
  --     = from
  --   ; to-from
  --     = λ y → sub just (to-from y)
  --   }

module _
  {A B : Set}
  where

  module RetractionPartial
    (F : Retraction A B)
    where

    to
      : A
      → Maybe B
    to x
      = just (Retraction.to F x)

    from
      : B
      → A
    from
      = Retraction.from F

    to-from
      : (y : B)
      → to (from y) ≡ just y
    to-from y
      = sub just (Retraction.to-from F y)

  retraction-partial
    : Retraction A B
    → PartialRetraction A B
  retraction-partial F
    = record {RetractionPartial F}

-- ### Identity

partial-retraction-identity
  : (A : Set)
  → PartialRetraction A A
partial-retraction-identity A
  = retraction-partial
    (retraction-identity A)

-- ### Compose

module _
  {A B C : Set}
  where

  module PartialRetractionCompose
    (F : PartialRetraction B C)
    (G : PartialRetraction A B)
    where

    to
      : A
      → Maybe C
    to x
      with PartialRetraction.to G x
    ... | nothing
      = nothing
    ... | just y
      = PartialRetraction.to F y

    from
      : C
      → A
    from
      = PartialRetraction.from G
      ∘ PartialRetraction.from F

    to-from
      : (y : C)
      → to (from y) ≡ just y
    to-from y
      with PartialRetraction.to G (PartialRetraction.from G
        (PartialRetraction.from F y))
      | PartialRetraction.to-from G
        (PartialRetraction.from F y)
    ... | _ | refl
      = PartialRetraction.to-from F y

  partial-retraction-compose
    : PartialRetraction B C
    → PartialRetraction A B
    → PartialRetraction A C
  partial-retraction-compose F G
    = record {PartialRetractionCompose F G}

