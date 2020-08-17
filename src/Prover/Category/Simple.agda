module Prover.Category.Simple where

open import Prover.Category
  using (Category)
open import Prover.Function
  using (Function; FunctionCompose; FunctionIdentity)

-- ## SimpleDependentCategory

record SimpleDependentCategory
  (C : Category)
  : Set₁
  where

  field

    set
      : Category.Object C
      → Set

    function
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → Function (set x) (set y)

    function-identity
      : (x : Category.Object C)
      → FunctionIdentity
        (function (Category.identity C x))

    function-compose
      : {x y z : Category.Object C}
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → FunctionCompose
        (function f)
        (function g)
        (function (Category.compose C f g))

