module Prover.Category.Weak.Sigma.Maybe where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; Functor; FunctorSquare)
open import Prover.Category.Maybe
  using (dependent-category-maybe)
open import Prover.Category.Sigma
  using (module CategorySigma)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-may; functor-sigma-may; functor-sigma-may₁;
    functor-square-sigma-may₁)
open import Prover.Category.Weak
  using (WeakFunctor; WeakFunctorSquare)
open import Prover.Prelude

-- ## WeakFunctor₁

module _
  {C₁ : Category}
  where

  module WeakFunctorSigmaMay₁
    (C₂ : DependentCategory C₁)
    where

    open Functor (functor-sigma-may₁ C₂) using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    map
      : (x y : Category.Object (category-sigma-may C₂))
      → Category.Arrow C₁ (unbase x) (unbase y)
      → Category.Arrow (category-sigma-may C₂) x y
    map (_ , x₂) _ f₁
      = record
      { domain
        = DependentCategory.base C₂ f₁ x₂
      ; arrow₁
        = f₁
      ; arrow₂
        = nothing
      ; valid
        = refl
      }

    abstract

      map-compose
        : (x y z : Category.Object (category-sigma-may C₂))
        → (f₁ : Category.Arrow C₁ (unbase y) (unbase z))
        → (g₁ : Category.Arrow C₁ (unbase x) (unbase y))
        → map x z (Category.compose C₁ f₁ g₁)
          ≡ Category.compose (category-sigma-may C₂) (map y z f₁) (map x y g₁)
      map-compose (_ , x₂) _ (z₁ , _) f₁ g₁
        = CategorySigma.arrow-eq (dependent-category-maybe C₂) p₂ refl
          (Maybe.nothing-eq₂ (DependentCategory.Arrow C₂ z₁) p₂ refl)
        where p₂ = DependentCategory.base-compose C₂ f₁ g₁ x₂
  
      map-unmap₁₂
        : (x₁ : Category.Object C₁)
        → {x₂ y₁₂ y₂₂ z₂ : DependentCategory.Object C₂ x₁}
        → (p₂ : y₁₂ ≡ y₂₂)
        → (f₂ : DependentCategory.Arrow
          (dependent-category-maybe C₂) x₁ y₂₂ z₂)
        → DependentCategory.compose-eq
          (dependent-category-maybe C₂) x₁ {x' = x₂} p₂ f₂ nothing
        ≡ nothing
      map-unmap₁₂ _ refl nothing
        = refl
      map-unmap₁₂ _ refl (just _)
        = refl
  
      map-unmap₁
        : {y z : Category.Object (category-sigma-may C₂)}
        → (x : Category.Object (category-sigma-may C₂))
        → (f : Category.Arrow (category-sigma-may C₂) y z)
        → (g₁ : Category.Arrow C₁ (unbase x) (unbase y))
        → Category.compose
          (category-sigma-may C₂)
          (map y z (unmap f))
          (map x y g₁)
        ≡ Category.compose
          (category-sigma-may C₂) f
          (map x y g₁)
      map-unmap₁ {z = (z₁ , _)} _ (CategorySigma.arrow _ _ f₂ p₂) _
        = CategorySigma.arrow-eq
          (dependent-category-maybe C₂) refl refl
          (sym (map-unmap₁₂ z₁ p₂ f₂))
  
      map-unmap₂
        : {x y : Category.Object (category-sigma-may C₂)}
        → (z : Category.Object (category-sigma-may C₂))
        → (f₁ : Category.Arrow C₁ (unbase y) (unbase z))
        → (g : Category.Arrow (category-sigma-may C₂) x y)
        → Category.compose
          (category-sigma-may C₂)
          (map y z f₁)
          (map x y (unmap g))
        ≡ Category.compose
          (category-sigma-may C₂)
          (map y z f₁) g
      map-unmap₂ (z₁ , _) f₁ (CategorySigma.arrow _ _ _ p₂)
        = CategorySigma.arrow-eq (dependent-category-maybe C₂) q₂ refl
          (Maybe.nothing-eq₂ (DependentCategory.Arrow C₂ z₁) q₂ refl)
        where q₂ = sub (DependentCategory.base C₂ f₁) p₂

  weak-functor-sigma-may₁
    : (C₂ : DependentCategory C₁)
    → WeakFunctor (functor-sigma-may₁ C₂)
  weak-functor-sigma-may₁ C₂
    = record {WeakFunctorSigmaMay₁ C₂}

-- ## WeakFunctorSquare₁

module _
  {C₁₁ C₂₁ : Category}
  {C₁₂ : DependentCategory C₁₁}
  {C₂₂ : DependentCategory C₂₁}
  where

  module WeakFunctorSquareSigmaMay₁
    (F : DependentFunctor C₁₂ C₂₂)
    where

    map
      : (x₁ y₁ : Category.Object (category-sigma-may C₁₂))
      → (f₁₁ : Category.Arrow C₁₁
        (Functor.base (functor-sigma-may₁ C₁₂) x₁)
        (Functor.base (functor-sigma-may₁ C₁₂) y₁))
      → WeakFunctor.map-eq
        (weak-functor-sigma-may₁ C₂₂)
        (Functor.base (functor-sigma-may F) x₁)
        (Functor.base (functor-sigma-may F) y₁)
        (FunctorSquare.base (functor-square-sigma-may₁ F) x₁)
        (FunctorSquare.base (functor-square-sigma-may₁ F) y₁)
        (Functor.map (DependentFunctor.functor F) f₁₁)
      ≡ Functor.map (functor-sigma-may F)
        (WeakFunctor.map (weak-functor-sigma-may₁ C₁₂) x₁ y₁ f₁₁)
    map (_ , x₁₂) y₁ f₁₁
      = CategorySigma.arrow-eq
        (dependent-category-maybe C₂₂) p₂₂ refl
        (Maybe.nothing-eq₂
          (DependentCategory.Arrow C₂₂
            (DependentFunctor.base F
              (Functor.base (functor-sigma-may₁ C₁₂) y₁))) p₂₂ refl)
      where p₂₂ = sym (DependentFunctor.base-commutative F f₁₁ x₁₂)

  weak-functor-square-sigma-may₁
    : (F : DependentFunctor C₁₂ C₂₂)
    → WeakFunctorSquare
      (weak-functor-sigma-may₁ C₁₂)
      (weak-functor-sigma-may₁ C₂₂)
      (functor-square-sigma-may₁ F)
  weak-functor-square-sigma-may₁ F
    = record {WeakFunctorSquareSigmaMay₁ F}

