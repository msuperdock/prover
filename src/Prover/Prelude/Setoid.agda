module Prover.Prelude.Setoid where

open import Prover.Prelude.Equal
  using (_≡_)

-- ## Definition

record Setoid
  : Set₁
  where

  field

    Element
      : Set

    ElementEqual
      : Element
      → Element
      → Set

    element-refl
      : {x : Element}
      → ElementEqual x x

    element-sym
      : {x₁ x₂ : Element}
      → ElementEqual x₁ x₂
      → ElementEqual x₂ x₁

    element-trans
      : {x₁ x₂ x₃ : Element}
      → ElementEqual x₁ x₂
      → ElementEqual x₂ x₃
      → ElementEqual x₁ x₃

-- ## Isomorphism

record SetoidIsomorphism
  (A : Set)
  (B : Setoid)
  : Set
  where

  field

    to
      : A
      → Setoid.Element B

    from
      : Setoid.Element B
      → A

    from-eq
      : {x₁ x₂ : Setoid.Element B}
      → Setoid.ElementEqual B x₁ x₂
      → from x₁ ≡ from x₂

    from-to
      : (x : A)
      → from (to x) ≡ x

    to-from
      : (x : Setoid.Element B)
      → Setoid.ElementEqual B (to (from x)) x

