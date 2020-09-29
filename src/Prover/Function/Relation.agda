module Prover.Function.Relation where

open import Prover.Function
  using (Function)
open import Prover.Prelude

-- ## FunctionInjective

record FunctionInjective
  {A B : Set}
  (R : Relation A)
  (S : Relation B)
  (F : Function A B)
  : Set
  where

  field

    base
      : Injective R S
        (Function.base F)

