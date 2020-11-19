module Prover.Category.Split.Induced where

open import Prover.Category
  using (Category; Precategory)
open import Prover.Category.Induced
  using (category-induced; functor-induced)
open import Prover.Category.Partial.Induced
  using (partial-functor-induced)
open import Prover.Category.Split
  using (SplitFunctor; SplitPrefunctor)

-- ## SplitFunctor

split-functor-induced
  : {C : Category}
  → {D : Precategory}
  → (F : SplitPrefunctor C D)
  → SplitFunctor C
    (category-induced F)
split-functor-induced F
  = record
  { SplitPrefunctor F
  ; partial-functor
    = partial-functor-induced F
  ; functor
    = functor-induced F
  }

