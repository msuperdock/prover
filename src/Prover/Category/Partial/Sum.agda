module Prover.Category.Partial.Sum where

open import Prover.Category
  using (Category; Functor; FunctorSquare)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Sum
  using (module CategorySum; category-sum; functor-sum)
open import Prover.Category.Weak
  using (WeakFunctor; WeakFunctorSquare)
open import Prover.Prelude

-- ## PartialFunctor₂

module _
  {C₁ C₂ : Category}
  {F : Functor C₂ C₁}
  where

  module PartialFunctorSum₂
    (F' : WeakFunctor F)
    where

    base
      : Category.Object (category-sum F)
      → Maybe (Category.Object C₂)
    base (ι₁ _)
      = nothing
    base (ι₂ x₂)
      = just x₂

    map
      : {x y : Category.Object (category-sum F)}
      → {x' y' : Category.Object C₂}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow (category-sum F) x y
      → Category.Arrow C₂ x' y'
    map {x = ι₂ x₂} {y = ι₂ y₂} refl refl
      (CategorySum.arrow₁ f₁)
      = WeakFunctor.map F' x₂ y₂ f₁
    map refl refl
      (CategorySum.arrow₂ f₂)
      = f₂

    abstract

      map-equal
        : {x y : Category.Object (category-sum F)}
        → {x' y' : Category.Object C₂}
        → {f₁ f₂ : Category.Arrow (category-sum F) x y}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → Category.ArrowEqual (category-sum F) f₁ f₂
        → Category.ArrowEqual C₂ (map p q f₁) (map p q f₂)
      map-equal {x = ι₂ x₂} {y = ι₂ y₂} refl refl
        (CategorySum.arrow₁-equal p₁)
        = WeakFunctor.map-equal F' x₂ y₂ p₁
      map-equal refl refl
        (CategorySum.arrow₂-equal p₂)
        = p₂

      map-identity
        : {x' : Category.Object C₂}
        → (x : Category.Object (category-sum F))
        → (p : base x ≡ just x')
        → Category.ArrowEqual C₂
          (map p p (Category.identity (category-sum F) x))
          (Category.identity C₂ x')
      map-identity (ι₂ _) refl
        = Category.arrow-refl C₂
  
      map-compose
        : {x y z : Category.Object (category-sum F)}
        → {x' y' z' : Category.Object C₂}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow (category-sum F) y z)
        → (g : Category.Arrow (category-sum F) x y)
        → Category.ArrowEqual C₂
          (map p r (Category.compose (category-sum F) f g))
          (Category.compose C₂ (map q r f) (map p q g))
      map-compose {x = ι₂ x₂} {y = ι₂ y₂} {z = ι₂ z₂} refl refl refl
        (CategorySum.arrow₁ f₁)
        (CategorySum.arrow₁ g₁)
        = WeakFunctor.map-compose F' x₂ y₂ z₂ f₁ g₁
      map-compose {x = ι₂ x₂} {y = ι₂ y₂} {z = ι₂ z₂} refl refl refl
        (CategorySum.arrow₁ f₁)
        (CategorySum.arrow₂ g₂)
        = Category.arrow-trans C₂ (WeakFunctor.map-compose F' x₂ y₂ z₂ f₁
          (Functor.map F g₂))
        $ WeakFunctor.map-unmap₂ F' z₂ f₁ g₂
      map-compose {x = ι₂ x₂} {y = ι₂ y₂} {z = ι₂ z₂} refl refl refl
        (CategorySum.arrow₂ f₂)
        (CategorySum.arrow₁ g₁)
        = Category.arrow-trans C₂ (WeakFunctor.map-compose F' x₂ y₂ z₂
          (Functor.map F f₂) g₁)
        $ WeakFunctor.map-unmap₁ F' x₂ f₂ g₁
      map-compose refl refl refl
        (CategorySum.arrow₂ _)
        (CategorySum.arrow₂ _)
        = Category.arrow-refl C₂

  partial-functor-sum₂
    : WeakFunctor F
    → PartialFunctor (category-sum F) C₂
  partial-functor-sum₂ F'
    = record {PartialFunctorSum₂ F'}

-- ## PartialFunctorSquare₂

module _
  {C₁₁ C₁₂ C₂₁ C₂₂ : Category}
  {F₁ : Functor C₂₁ C₁₁}
  {F₂ : Functor C₂₂ C₁₂}
  {F₁' : WeakFunctor F₁}
  {F₂' : WeakFunctor F₂}
  {G₁ : Functor C₁₁ C₁₂}
  {G₂ : Functor C₂₁ C₂₂}
  where

  module PartialFunctorSquareSum₂
    (s : FunctorSquare G₂ G₁ F₁ F₂)
    (s' : WeakFunctorSquare G₁ G₂ F₁' F₂')
    where

    base
      : {x₁' : Category.Object C₂₁}
      → (x₁ : Category.Object (category-sum F₁))
      → PartialFunctor.base (partial-functor-sum₂ F₁') x₁ ≡ just x₁'
      → PartialFunctor.base (partial-functor-sum₂ F₂')
        (Functor.base (functor-sum s) x₁)
      ≡ just (Functor.base G₂ x₁')
    base (ι₂ _) refl
      = refl

    map
      : {x₁ y₁ : Category.Object (category-sum F₁)}
      → {x₁' y₁' : Category.Object C₂₁}
      → (p₁ : PartialFunctor.base (partial-functor-sum₂ F₁') x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-sum₂ F₁') y₁ ≡ just y₁')
      → (f₁ : Category.Arrow (category-sum F₁) x₁ y₁)
      → Category.ArrowEqual C₂₂
        (PartialFunctor.map (partial-functor-sum₂ F₂') (base x₁ p₁) (base y₁ q₁)
          (Functor.map (functor-sum s) f₁))
        (Functor.map G₂
          (PartialFunctor.map (partial-functor-sum₂ F₁') p₁ q₁ f₁))
    map {x₁ = ι₂ x₂₁} {y₁ = ι₂ y₂₁} refl refl (CategorySum.arrow₁ f₁₁)
      = WeakFunctorSquare.map' s' x₂₁ y₂₁
        (FunctorSquare.base s x₂₁)
        (FunctorSquare.base s y₂₁) f₁₁
      $ Category.arrow-equal' C₁₂
        (FunctorSquare.base s x₂₁)
        (FunctorSquare.base s y₂₁)
        (Functor.map G₁ f₁₁)
    map refl refl (CategorySum.arrow₂ _)
      = Category.arrow-refl C₂₂

  partial-functor-square-sum₂
    : (s : FunctorSquare G₂ G₁ F₁ F₂)
    → WeakFunctorSquare G₁ G₂ F₁' F₂'
    → PartialFunctorSquare
      (functor-sum s) G₂
      (partial-functor-sum₂ F₁')
      (partial-functor-sum₂ F₂')
  partial-functor-square-sum₂ s s'
    = record {PartialFunctorSquareSum₂ s s'}

