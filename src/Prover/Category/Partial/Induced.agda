module Prover.Category.Partial.Induced where

open import Prover.Category
  using (Category; Precategory)
open import Prover.Category.Induced
  using (category-induced)
open import Prover.Category.Partial
  using (PartialFunctor; PartialPrefunctor)
open import Prover.Category.Split
  using (SplitPrefunctor)

-- ## PartialFunctor

partial-functor-induced
  : {C : Category}
  → {D : Precategory}
  → (F : SplitPrefunctor C D)
  → PartialFunctor C
    (category-induced F)
partial-functor-induced F
  = record {PartialPrefunctor (SplitPrefunctor.partial-prefunctor F)}

