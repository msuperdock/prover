module Prover.Category.Split.Sigma where

open import Prover.Category
  using (Category; Functor; functor-square-identity)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Dependent1.Split
  using (Dependent₁SplitFunctor; Dependent₁SplitFunctorSquare)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Sigma
  using (partial-functor-sigma; partial-functor-square-sigma)
open import Prover.Category.Sigma
  using (module CategorySigma; category-sigma; functor-sigma;
    functor-square-sigma)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Prelude

-- ## SplitFunctor

module _
  {C₁ : Category}
  {C₂ D₂ : Dependent₁Category C₁}
  where

  module SplitFunctorSigma
    (F₂ : Dependent₁SplitFunctor C₂ D₂)
    where

    partial-functor
      : PartialFunctor
        (category-sigma C₂)
        (category-sigma D₂)
    partial-functor
      = partial-functor-sigma
        (Dependent₁SplitFunctor.dependent₁-partial-functor F₂)

    open PartialFunctor partial-functor

    functor
      : Functor
        (category-sigma D₂)
        (category-sigma C₂)
    functor
      = functor-sigma
        (Dependent₁SplitFunctor.dependent₁-functor F₂)

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase
        : (x : Category.Object (category-sigma D₂))
        → base (unbase x) ≡ just x
      base-unbase (x₁ , x₂)
        with Dependent₁SplitFunctor.base F₂ x₁
          (Dependent₁SplitFunctor.unbase F₂ x₁ x₂)
        | Dependent₁SplitFunctor.base-unbase F₂ x₁ x₂
      ... | _ | refl
        = refl
  
      map-unmap
        : {x y : Category.Object (category-sigma D₂)}
        → (f : Category.Arrow (category-sigma D₂) x y)
        → Category.ArrowEqual
          (category-sigma D₂)
          (map (base-unbase x) (base-unbase y) (unmap f)) f
      map-unmap {x = (x₁ , x₂)} {y = (y₁ , y₂)}
        (CategorySigma.arrow f₁ f₂ refl)
        with Dependent₁SplitFunctor.base F₂ x₁
          (Dependent₁SplitFunctor.unbase F₂ x₁ x₂)
        | inspect (Dependent₁SplitFunctor.base F₂ x₁)
          (Dependent₁SplitFunctor.unbase F₂ x₁ x₂)
        | Dependent₁SplitFunctor.base-unbase F₂ x₁ x₂
        | Dependent₁SplitFunctor.base F₂ y₁
          (Dependent₁SplitFunctor.unbase F₂ y₁ y₂)
        | inspect (Dependent₁SplitFunctor.base F₂ y₁)
          (Dependent₁SplitFunctor.unbase F₂ y₁ y₂)
        | Dependent₁SplitFunctor.base-unbase F₂ y₁ y₂
      ... | _ | [ q₂ ] | refl | _ | [ r₂ ] | refl
        = record
        { arrow₁
          = Category.arrow-refl C₁
        ; arrow₂
          = Dependent₁SplitFunctor.map-unmap'' F₂ y₁ p₂' r₂ f₂
        }
        where
          p₂' = trans
            (sub (Dependent₁SplitFunctor.base F₂ y₁) (sym (trans (sym
              (Dependent₁SplitFunctor.unbase-square F₂ f₁ x₂)) refl)))
            (Dependent₁SplitFunctor.base-square F₂ f₁
              (Dependent₁SplitFunctor.unbase F₂ x₁ x₂) q₂)
            
      normalize-arrow
        : {x' : Category.Object (category-sigma D₂)}
        → (x : Category.Object (category-sigma C₂))
        → base x ≡ just x'
        → Category.Arrow (category-sigma C₂) x (unbase x')
      normalize-arrow (x₁ , x₂) _
        with Dependent₁SplitFunctor.base F₂ x₁ x₂
        | inspect (Dependent₁SplitFunctor.base F₂ x₁) x₂
      normalize-arrow (x₁ , x₂) refl | just _ | [ p₂ ]
        = record
        { arrow₁
          = Category.identity C₁ x₁
        ; arrow₂
          = Dependent₁SplitFunctor.normalize-arrow F₂ x₁ x₂ p₂
        ; valid
          = Dependent₁Category.base-identity C₂ x₁ x₂
        }

      normalize-valid
        : {x' : Category.Object (category-sigma D₂)}
        → (x : Category.Object (category-sigma C₂))
        → (p : base x ≡ just x')
        → Category.ArrowEqual
          (category-sigma D₂)
          (map p (base-unbase x') (normalize-arrow x p))
          (Category.identity (category-sigma D₂) x')
      normalize-valid (x₁ , x₂) _
        with Dependent₁SplitFunctor.base F₂ x₁ x₂
        | inspect (Dependent₁SplitFunctor.base F₂ x₁) x₂
      normalize-valid (x₁ , x₂) refl | just x₂' | [ p₂ ]
        with Dependent₁SplitFunctor.base F₂ x₁
          (Dependent₁SplitFunctor.unbase F₂ x₁ x₂')
        | inspect (Dependent₁SplitFunctor.base F₂ x₁)
          (Dependent₁SplitFunctor.unbase F₂ x₁ x₂')
        | Dependent₁SplitFunctor.base-unbase F₂ x₁ x₂'
      ... | just _ | [ q₂ ] | refl
        = record
        { arrow₁
          = Category.arrow-refl C₁
        ; arrow₂
          = Dependent₁SplitFunctor.normalize-valid' F₂ x₁ x₂ p₂ p₂' q₂
        }
        where
          p₂' = trans
            (sub (Dependent₁SplitFunctor.base F₂ x₁)
              (sym (Dependent₁Category.base-identity C₂ x₁ x₂)))
            (Dependent₁SplitFunctor.base-square F₂
              (Category.identity C₁ x₁) x₂ p₂)

  split-functor-sigma
    : Dependent₁SplitFunctor C₂ D₂
    → SplitFunctor
      (category-sigma C₂)
      (category-sigma D₂)
  split-functor-sigma F₂
    = record {SplitFunctorSigma F₂}

-- ## SplitFunctorSquare

split-functor-square-sigma
  : {C₁₁ C₂₁ : Category}
  → {C₁₂ D₁₂ : Dependent₁Category C₁₁}
  → {C₂₂ D₂₂ : Dependent₁Category C₂₁}
  → {F₁ : Functor C₁₁ C₂₁}
  → {F₂ : Dependent₁Functor C₁₂ C₂₂ F₁}
  → {G₂ : Dependent₁Functor D₁₂ D₂₂ F₁}
  → {H₁₂ : Dependent₁SplitFunctor C₁₂ D₁₂}
  → {H₂₂ : Dependent₁SplitFunctor C₂₂ D₂₂}
  → Dependent₁SplitFunctorSquare F₂ G₂ H₁₂ H₂₂
  → SplitFunctorSquare
    (functor-sigma F₂)
    (functor-sigma G₂)
    (split-functor-sigma H₁₂)
    (split-functor-sigma H₂₂)
split-functor-square-sigma {F₁ = F₁} s
  = record
  { partial-functor
    = partial-functor-square-sigma
      (Dependent₁SplitFunctorSquare.dependent₁-partial-functor s)
  ; functor
    = functor-square-sigma
      (functor-square-identity F₁)
      (Dependent₁SplitFunctorSquare.dependent₁-functor s)
  }

