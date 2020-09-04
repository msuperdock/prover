module Prover.Category.Dependent1.Unit where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity)
open import Prover.Category.Dependent1
  using (Dependent₁Category)
open import Prover.Category.Dependent1.Simple
  using (Dependent₁SimpleCategory)
open import Prover.Category.Unit
  using (category-unit; functor-compose-unit; functor-identity-unit;
    functor-unit)
open import Prover.Prelude

-- ## Dependent₁Category

module _
  {C : Category}
  where

  module Dependent₁CategoryUnit
    (A : Dependent₁SimpleCategory C)
    where

    category
      : Category.Object C
      → Category
    category x
      = category-unit
        (Dependent₁SimpleCategory.set A x)

    functor
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → Functor
        (category x)
        (category y)
    functor f
      = functor-unit
        (Dependent₁SimpleCategory.function A f)

    abstract

      functor-identity
        : (x : Category.Object C)
        → FunctorIdentity
          (functor (Category.identity C x))
      functor-identity x
        = functor-identity-unit
          (Dependent₁SimpleCategory.function A (Category.identity C x))
          (Dependent₁SimpleCategory.function-identity A x)
  
      functor-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → FunctorCompose
          (functor f)
          (functor g)
          (functor (Category.compose C f g))
      functor-compose f g
        = functor-compose-unit
          (Dependent₁SimpleCategory.function A f)
          (Dependent₁SimpleCategory.function A g)
          (Dependent₁SimpleCategory.function A (Category.compose C f g))
          (Dependent₁SimpleCategory.function-compose A f g)

  dependent₁-category-unit
    : Dependent₁SimpleCategory C
    → Dependent₁Category C
  dependent₁-category-unit A
    = record {Dependent₁CategoryUnit A}

