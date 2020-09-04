module Prover.Category.Split.Maybe where

open import Prover.Category
  using (Category; Functor; FunctorSquare)
open import Prover.Category.Maybe
  using (category-maybe; functor-maybe; functor-square-maybe)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Partial.Maybe
  using (partial-functor-maybe; partial-functor-square-maybe)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare; SplitFunctorSquare';
    split-functor-square')
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
        : (x' : Category.Object (category-maybe D))
        → base (unbase x') ≡ just x'
      base-unbase x'
        = SplitFunctor.base-unbase F x'
  
      map-unmap
        : {x' y' : Category.Object (category-maybe D)}
        → (f' : Category.Arrow (category-maybe D) x' y')
        → map (base-unbase x') (base-unbase y') (unmap f') ≡ f'
      map-unmap nothing
        = refl
      map-unmap (just f')
        = sub just (SplitFunctor.map-unmap F f')

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
        → map p (base-unbase x') (normalize-arrow x p)
          ≡ Category.identity (category-maybe D) x'
      normalize-valid x p
        = sub just (SplitFunctor.normalize-valid F x p)

  split-functor-maybe
    : SplitFunctor C D
    → SplitFunctor
      (category-maybe C)
      (category-maybe D)
  split-functor-maybe F
    = record {SplitFunctorMaybe F}

-- ## SplitFunctorSquare

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : SplitFunctor C₁ D₁}
  {H₂ : SplitFunctor C₂ D₂}
  where

  module SplitFunctorSquareMaybe
    (s : SplitFunctorSquare F G H₁ H₂)
    where

    partial-functor 
      : PartialFunctorSquare
        (functor-maybe F)
        (functor-maybe G)
        (SplitFunctor.partial-functor (split-functor-maybe H₁))
        (SplitFunctor.partial-functor (split-functor-maybe H₂))
    partial-functor
      = partial-functor-square-maybe
        (SplitFunctorSquare.partial-functor s)

    functor
      : FunctorSquare
        (functor-maybe G)
        (functor-maybe F)
        (SplitFunctor.functor (split-functor-maybe H₁))
        (SplitFunctor.functor (split-functor-maybe H₂))
    functor
      = functor-square-maybe
        (SplitFunctorSquare.functor s)

  split-functor-square-maybe
    : SplitFunctorSquare F G H₁ H₂
    → SplitFunctorSquare
      (functor-maybe F)
      (functor-maybe G)
      (split-functor-maybe H₁)
      (split-functor-maybe H₂)
  split-functor-square-maybe s
    = record {SplitFunctorSquareMaybe s}

-- ## SplitFunctorSquare'

split-functor-square-maybe'
  : {C₁ C₂ D₁ D₂ D₃ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₃}
  → {H₁ : SplitFunctor C₁ D₁}
  → {H₂ : SplitFunctor C₂ D₂}
  → SplitFunctorSquare' F G H₁ H₂
  → SplitFunctorSquare'
    (functor-maybe F)
    (functor-maybe G)
    (split-functor-maybe H₁)
    (split-functor-maybe H₂)
split-functor-square-maybe' (split-functor-square' s)
  = split-functor-square' (split-functor-square-maybe s)

