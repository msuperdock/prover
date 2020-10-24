module Prover.Category.Split.Unit where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Unit
  using (partial-functor-unit; partial-functor-square-unit)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Category.Unit
  using (module CategoryUnit; category-unit; functor-unit; functor-square-unit)
open import Prover.Function
  using (Function)
open import Prover.Function.Split
  using (SplitFunction; SplitFunctionSquare)
open import Prover.Prelude

-- ## SplitFunctor

module _
  {A B : Set}
  where

  module SplitFunctorUnit
    (F : SplitFunction A B)
    where

    partial-functor
      : PartialFunctor
        (category-unit A)
        (category-unit B)
    partial-functor
      = partial-functor-unit
        (SplitFunction.partial-function F)

    open PartialFunctor partial-functor

    functor
      : Functor
        (category-unit B)
        (category-unit A)
    functor
      = functor-unit
        (SplitFunction.function F)

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase
        : (x : Category.Object (category-unit B))
        → base (unbase x) ≡ just x
      base-unbase
        = SplitFunction.base-unbase F
  
      map-unmap
        : {x y : Category.Object (category-unit B)}
        → (f : Category.Arrow (category-unit B) x y)
        → Category.ArrowEqual (category-unit B)
          (map (base-unbase x) (base-unbase y) (unmap f)) f
      map-unmap CategoryUnit.arrow
        = refl
  
      normalize-arrow
        : {x' : Category.Object (category-unit B)}
        → (x : Category.Object (category-unit A))
        → base x ≡ just x'
        → Category.Arrow (category-unit A) x (unbase x')
      normalize-arrow _ _
        = CategoryUnit.arrow
  
      normalize-valid
        : {x' : Category.Object (category-unit B)}
        → (x : Category.Object (category-unit A))
        → (p : base x ≡ just x')
        → Category.ArrowEqual (category-unit B)
          (map p (base-unbase x') (normalize-arrow x p))
          (Category.identity (category-unit B) x')
      normalize-valid _ _
        = refl

  split-functor-unit
    : SplitFunction A B
    → SplitFunctor
      (category-unit A)
      (category-unit B)
  split-functor-unit r
    = record {SplitFunctorUnit r}

-- ## SplitFunctorSquare

split-functor-square-unit
  : {A₁ A₂ B₁ B₂ : Set}
  → {F : Function A₁ A₂}
  → {G : Function B₁ B₂}
  → {H₁ : SplitFunction A₁ B₁}
  → {H₂ : SplitFunction A₂ B₂}
  → SplitFunctionSquare F G H₁ H₂
  → SplitFunctorSquare
    (functor-unit F)
    (functor-unit G)
    (split-functor-unit H₁)
    (split-functor-unit H₂)
split-functor-square-unit s
  = record
  { partial-functor
    = partial-functor-square-unit
      (SplitFunctionSquare.partial-function s)
  ; functor
    = functor-square-unit
      (SplitFunctionSquare.function s)
  }

