module Prover.Prelude.Inspect where

open import Prover.Prelude.Equality
  using (_≡_; refl)

module _
  {A : Set}
  {B : A → Set}
  where

  data Inspect
    (f : (x : A) → B x)
    (x : A)
    (y : B x)
    : Set
    where
  
    [_]
      : f x ≡ y
      → Inspect f x y
  
  inspect
    : (f : (x : A) → B x)
    → (x : A)
    → Inspect f x (f x)
  inspect f x
    = [ refl ]

