module Prover.Category.Split.Sum where

open import Prover.Category
  using (Category; Functor; FunctorSquare)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Partial.Sum
  using (partial-functor-sum₂; partial-functor-square-sum₂)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Category.Sum
  using (module CategorySum; category-sum; functor-sum; functor-sum₂;
    functor-square-sum₂)
open import Prover.Category.Weak
  using (WeakFunctor; WeakFunctorSquare)
open import Prover.Prelude

-- ## SplitFunctor₂

module _
  {C₁ C₂ D : Category}
  {F : Functor C₂ C₁}
  where

  module SplitFunctorSum₂
    (F' : WeakFunctor F)
    (G : SplitFunctor C₂ D)
    where

    partial-functor
      : PartialFunctor (category-sum F) D
    partial-functor
      = partial-functor-sum₂ F' (SplitFunctor.partial-functor G)

    open PartialFunctor partial-functor

    functor
      : Functor D (category-sum F)
    functor
      = functor-sum₂ F (SplitFunctor.functor G)

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      ; map-identity
        to unmap-identity
      ; map-compose
        to unmap-compose
      )

    abstract

      base-unbase
        : (x' : Category.Object D)
        → base (unbase x') ≡ just x'
      base-unbase
        = SplitFunctor.base-unbase G
  
      map-unmap
        : {x' y' : Category.Object D}
        → (f' : Category.Arrow D x' y')
        → map (base-unbase x') (base-unbase y') (unmap f') ≡ f'
      map-unmap
        = SplitFunctor.map-unmap G
  
      normalize-arrow
        : {x' : Category.Object D}
        → (x : Category.Object (category-sum F))
        → base x ≡ just x'
        → Category.Arrow (category-sum F) x (unbase x')
      normalize-arrow (ι₂ x) p
        = CategorySum.arrow₂ (SplitFunctor.normalize-arrow G x p)

      normalize-valid
        : {x' : Category.Object D}
        → (x : Category.Object (category-sum F))
        → (p : base x ≡ just x')
        → map {x = x} p (base-unbase x') (normalize-arrow x p)
          ≡ Category.identity D x'
      normalize-valid (ι₂ x₂) p
        = SplitFunctor.normalize-valid G x₂ p

  split-functor-sum₂
    : WeakFunctor F
    → SplitFunctor C₂ D
    → SplitFunctor (category-sum F) D
  split-functor-sum₂ F' G
    = record {SplitFunctorSum₂ F' G}

-- ## SplitFunctorSquare₂

module _
  {C₁₁ C₁₂ C₂₁ C₂₂ D₁ D₂ : Category}
  {F₁ : Functor C₁₂ C₁₁}
  {F₂ : Functor C₂₂ C₂₁}
  {F₁' : WeakFunctor F₁}
  {F₂' : WeakFunctor F₂}
  {G₁ : SplitFunctor C₁₂ D₁}
  {G₂ : SplitFunctor C₂₂ D₂}
  {H₁ : Functor C₁₁ C₂₁}
  {H₂ : Functor C₁₂ C₂₂}
  {I : Functor D₁ D₂}
  {s : FunctorSquare H₂ H₁ F₁ F₂}
  where

  module SplitFunctorSquareSum₂
    (s' : WeakFunctorSquare F₁' F₂' s)
    (t : SplitFunctorSquare H₂ I G₁ G₂)
    where

    partial-functor
      : PartialFunctorSquare (functor-sum s) I
        (SplitFunctor.partial-functor (split-functor-sum₂ F₁' G₁))
        (SplitFunctor.partial-functor (split-functor-sum₂ F₂' G₂))
    partial-functor
      = partial-functor-square-sum₂ s'
        (SplitFunctorSquare.partial-functor t)

    functor
      : FunctorSquare I (functor-sum s)
        (SplitFunctor.functor (split-functor-sum₂ F₁' G₁))
        (SplitFunctor.functor (split-functor-sum₂ F₂' G₂))
    functor
      = functor-square-sum₂ s
        (SplitFunctorSquare.functor t)

  split-functor-square-sum₂
    : WeakFunctorSquare F₁' F₂' s
    → SplitFunctorSquare H₂ I G₁ G₂
    → SplitFunctorSquare
      (functor-sum s) I
      (split-functor-sum₂ F₁' G₁)
      (split-functor-sum₂ F₂' G₂)
  split-functor-square-sum₂ s' t
    = record {SplitFunctorSquareSum₂ s' t}

