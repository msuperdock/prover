module Prover.Category.Weak.Sigma.Maybe where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Dependent1.Maybe
  using (dependent₁-category-maybe)
open import Prover.Category.Maybe
  using (arrow-equal-nothing)
open import Prover.Category.Sigma
  using (module CategorySigma)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-maybe; functor-sigma-maybe; functor-sigma-maybe₁)
open import Prover.Category.Weak
  using (WeakFunctor; WeakFunctorSquare)
open import Prover.Prelude

-- ## WeakFunctor₁

module _
  {C₁ : Category}
  where

  module WeakFunctorSigmaMaybe₁
    (C₂ : Dependent₁Category C₁)
    where

    open Functor (functor-sigma-maybe₁ C₂) using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    map
      : (x y : Category.Object (category-sigma-maybe C₂))
      → Category.Arrow C₁ (unbase x) (unbase y)
      → Category.Arrow (category-sigma-maybe C₂) x y
    map _ _ f₁
      = record
      { arrow₁
        = f₁
      ; arrow₂
        = nothing
      ; valid
        = refl
      }

    abstract

      map-equal
        : (x y : Category.Object (category-sigma-maybe C₂))
        → {f₁₁ f₁₂ : Category.Arrow C₁ (unbase x) (unbase y)}
        → Category.ArrowEqual C₁ f₁₁ f₁₂
        → Category.ArrowEqual
          (category-sigma-maybe C₂)
          (map x y f₁₁)
          (map x y f₁₂)
      map-equal (_ , x₂) (y₁ , _) p₁
        = record
        { arrow₁
          = p₁
        ; arrow₂
          = arrow-equal-nothing
            (Dependent₁Category.category C₂ y₁)
            (Dependent₁Category.base-equal C₂ p₁ x₂) refl
        }

      map-compose
        : (x y z : Category.Object (category-sigma-maybe C₂))
        → (f₁ : Category.Arrow C₁ (unbase y) (unbase z))
        → (g₁ : Category.Arrow C₁ (unbase x) (unbase y))
        → Category.ArrowEqual
          (category-sigma-maybe C₂)
          (map x z (Category.compose C₁ f₁ g₁))
          (Category.compose (category-sigma-maybe C₂) (map y z f₁) (map x y g₁))
      map-compose (_ , x₂) _ (z₁ , _) f₁ g₁
        = record
        { arrow₁
          = Category.arrow-refl C₁
        ; arrow₂
          = arrow-equal-nothing
            (Dependent₁Category.category C₂ z₁)
            (Dependent₁Category.base-compose C₂ f₁ g₁ x₂) refl
        }

      map-unmap₁
        : {y z : Category.Object (category-sigma-maybe C₂)}
        → (x : Category.Object (category-sigma-maybe C₂))
        → (f : Category.Arrow (category-sigma-maybe C₂) y z)
        → (g₁ : Category.Arrow C₁ (unbase x) (unbase y))
        → Category.ArrowEqual
          (category-sigma-maybe C₂)
          (Category.compose
            (category-sigma-maybe C₂)
            (map y z (unmap f))
            (map x y g₁))
          (Category.compose
            (category-sigma-maybe C₂) f
            (map x y g₁))
      map-unmap₁ {z = (z₁ , _)} _ (CategorySigma.arrow _ nothing refl) _
        = record
        { arrow₁
          = Category.arrow-refl C₁
        ; arrow₂
          = Dependent₁Category.arrow-refl' (dependent₁-category-maybe C₂) z₁
        }
      map-unmap₁ {z = (z₁ , _)} _ (CategorySigma.arrow _ (just _) refl) _
        = record
        { arrow₁
          = Category.arrow-refl C₁
        ; arrow₂
          = Dependent₁Category.arrow-refl' (dependent₁-category-maybe C₂) z₁
        }

      map-unmap₂
        : {x y : Category.Object (category-sigma-maybe C₂)}
        → (z : Category.Object (category-sigma-maybe C₂))
        → (f₁ : Category.Arrow C₁ (unbase y) (unbase z))
        → (g : Category.Arrow (category-sigma-maybe C₂) x y)
        → Category.ArrowEqual
          (category-sigma-maybe C₂)
          (Category.compose
            (category-sigma-maybe C₂)
            (map y z f₁)
            (map x y (unmap g)))
          (Category.compose
            (category-sigma-maybe C₂)
            (map y z f₁) g)
      map-unmap₂ (z₁ , _) _ (CategorySigma.arrow _ _ refl)
        = record
        { arrow₁
          = Category.arrow-refl C₁
        ; arrow₂
          = Dependent₁Category.arrow-refl' (dependent₁-category-maybe C₂) z₁
        }

  weak-functor-sigma-maybe₁
    : (C₂ : Dependent₁Category C₁)
    → WeakFunctor (functor-sigma-maybe₁ C₂)
  weak-functor-sigma-maybe₁ C₂
    = record {WeakFunctorSigmaMaybe₁ C₂}

-- ## WeakFunctorSquare₁

module _
  {C₁₁ C₁₂ : Category}
  {C₂₁ : Dependent₁Category C₁₁}
  {C₂₂ : Dependent₁Category C₁₂}
  {F₁ : Functor C₁₁ C₁₂}
  where

  module WeakFunctorSquareSigmaMaybe₁
    (F₂ : Dependent₁Functor C₂₁ C₂₂ F₁)
    where

    map
      : (x₁ y₁ : Category.Object (category-sigma-maybe C₂₁))
      → (p : Functor.base (functor-sigma-maybe₁ C₂₂)
        (Functor.base (functor-sigma-maybe F₂) x₁)
        ≡ Functor.base F₁ (Functor.base (functor-sigma-maybe₁ C₂₁) x₁))
      → (q : Functor.base (functor-sigma-maybe₁ C₂₂)
        (Functor.base (functor-sigma-maybe F₂) y₁)
        ≡ Functor.base F₁ (Functor.base (functor-sigma-maybe₁ C₂₁) y₁))
      → (f₁₁ : Category.Arrow C₁₁
        (Functor.base (functor-sigma-maybe₁ C₂₁) x₁)
        (Functor.base (functor-sigma-maybe₁ C₂₁) y₁))
      → Category.ArrowEqual
        (category-sigma-maybe C₂₂)
        (WeakFunctor.map'
          (weak-functor-sigma-maybe₁ C₂₂)
          (Functor.base (functor-sigma-maybe F₂) x₁)
          (Functor.base (functor-sigma-maybe F₂) y₁) p q
          (Functor.map F₁ f₁₁))
        (Functor.map
          (functor-sigma-maybe F₂)
          (WeakFunctor.map (weak-functor-sigma-maybe₁ C₂₁) x₁ y₁ f₁₁))
    map (_ , x₂₁) (y₁₁ , _) refl refl f₁₁
      = record
      { arrow₁
        = Category.arrow-refl C₁₂
      ; arrow₂
        = arrow-equal-nothing
          (Dependent₁Category.category C₂₂ (Functor.base F₁ y₁₁))
          (sym (Dependent₁Functor.base-square F₂ f₁₁ x₂₁)) refl
      }

  weak-functor-square-sigma-maybe₁
    : (F₂ : Dependent₁Functor C₂₁ C₂₂ F₁)
    → WeakFunctorSquare F₁
      (functor-sigma-maybe F₂)
      (weak-functor-sigma-maybe₁ C₂₁)
      (weak-functor-sigma-maybe₁ C₂₂)
  weak-functor-square-sigma-maybe₁ F₂
    = record {WeakFunctorSquareSigmaMaybe₁ F₂}

