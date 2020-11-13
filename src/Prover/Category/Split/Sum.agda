module Prover.Category.Split.Sum where

open import Prover.Category
  using (Category; Functor; FunctorSquare)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Sum
  using (partial-functor-sum₂; partial-functor-square-sum₂)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Category.Sum
  using (category-sum; functor-sum; functor-sum₂; functor-square-sum₂)
open import Prover.Category.Weak
  using (WeakFunctor; WeakFunctorSquare)
open import Prover.Prelude

-- ## SplitFunctor₂

module _
  {C₁ C₂ : Category}
  {F : Functor C₂ C₁}
  where

  module SplitFunctorSum₂
    (F' : WeakFunctor F)
    where

    partial-functor
      : PartialFunctor (category-sum F) C₂
    partial-functor
      = partial-functor-sum₂ F'

    open PartialFunctor partial-functor

    functor
      : Functor C₂ (category-sum F)
    functor
      = functor-sum₂ F

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase
        : (x : Category.Object C₂)
        → base (unbase x) ≡ just x
      base-unbase _
        = refl
  
      map-unmap
        : {x y : Category.Object C₂}
        → (f : Category.Arrow C₂ x y)
        → Category.ArrowEqual C₂
          (map (base-unbase x) (base-unbase y) (unmap f)) f
      map-unmap _
        = Category.arrow-refl C₂
  
      normalize-arrow
        : {x' : Category.Object C₂}
        → (x : Category.Object (category-sum F))
        → base x ≡ just x'
        → Category.Arrow (category-sum F) x (unbase x')
      normalize-arrow (ι₂ x) refl
        = Category.identity (category-sum F) (ι₂ x)

      normalize-valid
        : {x' : Category.Object C₂}
        → (x : Category.Object (category-sum F))
        → (p : base x ≡ just x')
        → Category.ArrowEqual C₂
          (map p (base-unbase x') (normalize-arrow x p))
          (Category.identity C₂ x')
      normalize-valid (ι₂ _) refl
        = Category.arrow-refl C₂

  split-functor-sum₂
    : WeakFunctor F
    → SplitFunctor (category-sum F) C₂
  split-functor-sum₂ F'
    = record {SplitFunctorSum₂ F'}

-- ## SplitFunctorSquare₂

split-functor-square-sum₂
  : {C₁₁ C₁₂ C₂₁ C₂₂ : Category}
  → {F₁ : Functor C₁₂ C₁₁}
  → {F₂ : Functor C₂₂ C₂₁}
  → {F₁' : WeakFunctor F₁}
  → {F₂' : WeakFunctor F₂}
  → {G₁ : Functor C₁₁ C₂₁}
  → {G₂ : Functor C₁₂ C₂₂}
  → (s : FunctorSquare G₂ G₁ F₁ F₂)
  → WeakFunctorSquare G₁ G₂ F₁' F₂'
  → SplitFunctorSquare
    (functor-sum s) G₂
    (split-functor-sum₂ F₁')
    (split-functor-sum₂ F₂')
split-functor-square-sum₂ s s'
  = record
  { partial-functor
    = partial-functor-square-sum₂ s s'
  ; functor
    = functor-square-sum₂ s
  }

