module Prover.Category.Split.Product where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Product
  using (partial-functor-product; partial-functor-square-product)
open import Prover.Category.Product
  using (category-product; functor-product; functor-square-product)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Prelude

-- ## SplitFunctor

module _
  {C₁ C₂ D₁ D₂ : Category}
  where

  module SplitFunctorProduct
    (F₁ : SplitFunctor C₁ D₁)
    (F₂ : SplitFunctor C₂ D₂)
    where

    partial-functor
      : PartialFunctor
        (category-product C₁ C₂)
        (category-product D₁ D₂)
    partial-functor
      = partial-functor-product
        (SplitFunctor.partial-functor F₁)
        (SplitFunctor.partial-functor F₂)

    open PartialFunctor partial-functor

    functor
      : Functor
        (category-product D₁ D₂)
        (category-product C₁ C₂)
    functor
      = functor-product
        (SplitFunctor.functor F₁)
        (SplitFunctor.functor F₂)

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase
        : (x : Category.Object (category-product D₁ D₂))
        → base (unbase x) ≡ just x
      base-unbase (x₁ , x₂)
        with SplitFunctor.base F₁ (SplitFunctor.unbase F₁ x₁)
        | SplitFunctor.base-unbase F₁ x₁
        | SplitFunctor.base F₂ (SplitFunctor.unbase F₂ x₂)
        | SplitFunctor.base-unbase F₂ x₂
      ... | _ | refl | _ | refl
        = refl
  
      map-unmap
        : {x y : Category.Object (category-product D₁ D₂)}
        → (f : Category.Arrow (category-product D₁ D₂) x y)
        → Category.ArrowEqual (category-product D₁ D₂)
          (map (base-unbase x) (base-unbase y) (unmap f)) f
      map-unmap {x = (x₁ , x₂)} {y = (y₁ , y₂)} _
        with SplitFunctor.base F₁ (SplitFunctor.unbase F₁ x₁)
        | inspect (SplitFunctor.base F₁) (SplitFunctor.unbase F₁ x₁)
        | SplitFunctor.base-unbase F₁ x₁
        | SplitFunctor.base F₂ (SplitFunctor.unbase F₂ x₂)
        | inspect (SplitFunctor.base F₂) (SplitFunctor.unbase F₂ x₂)
        | SplitFunctor.base-unbase F₂ x₂
        | SplitFunctor.base F₁ (SplitFunctor.unbase F₁ y₁)
        | inspect (SplitFunctor.base F₁) (SplitFunctor.unbase F₁ y₁)
        | SplitFunctor.base-unbase F₁ y₁
        | SplitFunctor.base F₂ (SplitFunctor.unbase F₂ y₂)
        | inspect (SplitFunctor.base F₂) (SplitFunctor.unbase F₂ y₂)
        | SplitFunctor.base-unbase F₂ y₂
      map-unmap {x = (x₁ , x₂)} {y = (y₁ , y₂)} (f₁ , f₂)
        | just _ | [ p₁ ] | refl | just _ | [ p₂ ] | refl
        | just _ | [ q₁ ] | refl | just _ | [ q₂ ] | refl
        with irrelevant p₁ (SplitFunctor.base-unbase F₁ x₁)
        | irrelevant p₂ (SplitFunctor.base-unbase F₂ x₂)
        | irrelevant q₁ (SplitFunctor.base-unbase F₁ y₁)
        | irrelevant q₂ (SplitFunctor.base-unbase F₂ y₂)
      ... | refl | refl | refl | refl
        = SplitFunctor.map-unmap F₁ f₁
        , SplitFunctor.map-unmap F₂ f₂

      normalize-arrow
        : {x' : Category.Object (category-product D₁ D₂)}
        → (x : Category.Object (category-product C₁ C₂))
        → base x ≡ just x'
        → Category.Arrow (category-product C₁ C₂) x (unbase x')
      normalize-arrow (x₁ , x₂) _
        with SplitFunctor.base F₁ x₁
        | inspect (SplitFunctor.base F₁) x₁
        | SplitFunctor.base F₂ x₂
        | inspect (SplitFunctor.base F₂) x₂
      normalize-arrow (x₁ , x₂) refl
        | just _ | [ p₁ ] | just _ | [ p₂ ]
        = SplitFunctor.normalize-arrow F₁ x₁ p₁
        , SplitFunctor.normalize-arrow F₂ x₂ p₂

      normalize-valid
        : {x' : Category.Object (category-product D₁ D₂)}
        → (x : Category.Object (category-product C₁ C₂))
        → (p : base x ≡ just x')
        → Category.ArrowEqual (category-product D₁ D₂)
          (map p (base-unbase x') (normalize-arrow x p))
          (Category.identity (category-product D₁ D₂) x')
      normalize-valid {x' = (x₁' , x₂')} (x₁ , x₂) _
        with SplitFunctor.base F₁ x₁
        | inspect (SplitFunctor.base F₁) x₁
        | SplitFunctor.base F₂ x₂
        | inspect (SplitFunctor.base F₂) x₂
        | SplitFunctor.base F₁ (SplitFunctor.unbase F₁ x₁')
        | inspect (SplitFunctor.base F₁) (SplitFunctor.unbase F₁ x₁')
        | SplitFunctor.base-unbase F₁ x₁'
        | SplitFunctor.base F₂ (SplitFunctor.unbase F₂ x₂')
        | inspect (SplitFunctor.base F₂) (SplitFunctor.unbase F₂ x₂')
        | SplitFunctor.base-unbase F₂ x₂'
      normalize-valid {x' = (x₁' , x₂')} (x₁ , x₂) refl
        | just _ | [ p₁ ] | just _ | [ p₂ ]
        | just _ | [ p₁' ] | refl | just _ | [ p₂' ] | refl
        with irrelevant p₁' (SplitFunctor.base-unbase F₁ x₁')
        | irrelevant p₂' (SplitFunctor.base-unbase F₂ x₂')
      ... | refl | refl
        = SplitFunctor.normalize-valid F₁ x₁ p₁
        , SplitFunctor.normalize-valid F₂ x₂ p₂

  split-functor-product
    : SplitFunctor C₁ D₁
    → SplitFunctor C₂ D₂
    → SplitFunctor
      (category-product C₁ C₂)
      (category-product D₁ D₂)
  split-functor-product F₁ F₂
    = record {SplitFunctorProduct F₁ F₂}

-- ## SplitFunctorSquare

split-functor-square-product
  : {C₁₁ C₁₂ C₂₁ C₂₂ D₁₁ D₁₂ D₂₁ D₂₂ : Category}
  → {F₁ : Functor C₁₁ C₁₂}
  → {F₂ : Functor C₂₁ C₂₂}
  → {G₁ : Functor D₁₁ D₁₂}
  → {G₂ : Functor D₂₁ D₂₂}
  → {H₁₁ : SplitFunctor C₁₁ D₁₁}
  → {H₁₂ : SplitFunctor C₁₂ D₁₂}
  → {H₂₁ : SplitFunctor C₂₁ D₂₁}
  → {H₂₂ : SplitFunctor C₂₂ D₂₂}
  → SplitFunctorSquare F₁ G₁ H₁₁ H₁₂
  → SplitFunctorSquare F₂ G₂ H₂₁ H₂₂
  → SplitFunctorSquare
    (functor-product F₁ F₂)
    (functor-product G₁ G₂)
    (split-functor-product H₁₁ H₂₁)
    (split-functor-product H₁₂ H₂₂)
split-functor-square-product s₁ s₂
  = record
  { partial-functor 
    = partial-functor-square-product
      (SplitFunctorSquare.partial-functor s₁)
      (SplitFunctorSquare.partial-functor s₂)
  ; functor
    = functor-square-product
      (SplitFunctorSquare.functor s₁)
      (SplitFunctorSquare.functor s₂)
  }

