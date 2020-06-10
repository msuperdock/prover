module Prover.Category.Partial.Unit where

open import Prover.Category
  using (Category)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Unit
  using (module CategoryUnit; category-unit)
open import Prover.Prelude

module _
  {A B : Set}
  where

  module PartialFunctorUnit
    (f : A → Maybe B)
    where

    base
      : Category.Object (category-unit A)
      → Maybe (Category.Object (category-unit B))
    base
      = f

    map
      : {x y : Category.Object (category-unit A)}
      → {x' y' : Category.Object (category-unit B)}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow (category-unit A) x y
      → Category.Arrow (category-unit B) x' y'
    map _ _ _
      = CategoryUnit.arrow

    map-identity
      : {x' : Category.Object (category-unit B)}
      → (x : Category.Object (category-unit A))
      → (p : base x ≡ just x')
      → map p p (Category.identity (category-unit A) x)
        ≡ Category.identity (category-unit B) x'
    map-identity _ _
      = refl

    map-compose
      : {x y z : Category.Object (category-unit A)}
      → {x' y' z' : Category.Object (category-unit B)}
      → (p : base x ≡ just x')
      → (q : base y ≡ just y')
      → (r : base z ≡ just z')
      → (f : Category.Arrow (category-unit A) y z)
      → (g : Category.Arrow (category-unit A) x y)
      → map p r (Category.compose (category-unit A) f g)
        ≡ Category.compose (category-unit B) (map q r f) (map p q g)
    map-compose _ _ _ _ _
      = refl

  partial-functor-unit
    : (A → Maybe B)
    → PartialFunctor
      (category-unit A)
      (category-unit B)
  partial-functor-unit f
    = record {PartialFunctorUnit f}

