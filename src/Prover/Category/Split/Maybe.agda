module Prover.Category.Split.Maybe where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Maybe
  using (module CategoryMaybe; category-maybe; functor-maybe;
    functor-square-maybe)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Maybe
  using (partial-functor-maybe; partial-functor-square-maybe)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Prelude

-- ## SplitFunctor

module _
  {C D : Category}
  where

  module SplitFunctorMaybe
    (F : SplitFunctor C D)
    where
  
    partial-functor
      : PartialFunctor
        (category-maybe C)
        (category-maybe D)
    partial-functor
      = partial-functor-maybe
        (SplitFunctor.partial-functor F)

    open PartialFunctor partial-functor

    functor
      : Functor
        (category-maybe D)
        (category-maybe C)
    functor
      = functor-maybe
        (SplitFunctor.functor F)

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase
        : (x : Category.Object (category-maybe D))
        → base (unbase x) ≡ just x
      base-unbase x
        = SplitFunctor.base-unbase F x
  
      map-unmap
        : {x y : Category.Object (category-maybe D)}
        → (f : Category.Arrow (category-maybe D) x y)
        → Category.ArrowEqual
          (category-maybe D)
          (map (base-unbase x) (base-unbase y) (unmap f)) f
      map-unmap nothing
        = CategoryMaybe.nothing
      map-unmap (just f)
        = CategoryMaybe.just (SplitFunctor.map-unmap F f)

      normalize-arrow
        : {x' : Category.Object (category-maybe D)}
        → (x : Category.Object (category-maybe C))
        → base x ≡ just x'
        → Category.Arrow (category-maybe C) x (unbase x')
      normalize-arrow x p
        = just (SplitFunctor.normalize-arrow F x p)

      normalize-valid
        : {x' : Category.Object (category-maybe D)}
        → (x : Category.Object (category-maybe C))
        → (p : base x ≡ just x')
        → Category.ArrowEqual
          (category-maybe D)
          (map p (base-unbase x') (normalize-arrow x p))
          (Category.identity (category-maybe D) x')
      normalize-valid x p
        = CategoryMaybe.just (SplitFunctor.normalize-valid F x p)

  split-functor-maybe
    : SplitFunctor C D
    → SplitFunctor
      (category-maybe C)
      (category-maybe D)
  split-functor-maybe F
    = record {SplitFunctorMaybe F}

-- ## SplitFunctorSquare

split-functor-square-maybe
  : {C₁ C₂ D₁ D₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : SplitFunctor C₁ D₁}
  → {H₂ : SplitFunctor C₂ D₂}
  → SplitFunctorSquare F G H₁ H₂
  → SplitFunctorSquare
    (functor-maybe F)
    (functor-maybe G)
    (split-functor-maybe H₁)
    (split-functor-maybe H₂)
split-functor-square-maybe s
  = record
  { partial-functor
    = partial-functor-square-maybe
      (SplitFunctorSquare.partial-functor s)
  ; functor
    = functor-square-maybe
      (SplitFunctorSquare.functor s)
  }

