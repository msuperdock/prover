module Prover.Prelude.Retraction where

open import Prover.Prelude.Equal
  using (_≡_; refl)
open import Prover.Prelude.Function
  using (_∘_)

-- ## Definition

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

-- ## Compose

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

