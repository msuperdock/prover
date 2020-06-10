module Prover.Category.Partial.Sum where

open import Prover.Category
  using (Category; Functor; FunctorSquare)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Sum
  using (module CategorySum; module FunctorSum; category-sum; functor-sum)
open import Prover.Category.Weak
  using (WeakFunctor; WeakFunctorSquare)
open import Prover.Prelude

-- ## PartialFunctor₂

module _
  {C₁ C₂ D : Category}
  {F : Functor C₂ C₁}
  where

  module PartialFunctorSum₂
    (F' : WeakFunctor F)
    (G : PartialFunctor C₂ D)
    where

    base
      : Category.Object (category-sum F)
      → Maybe (Category.Object D)
    base (ι₁ _)
      = nothing
    base (ι₂ x₂)
      = PartialFunctor.base G x₂

    map
      : {x y : Category.Object (category-sum F)}
      → {x' y' : Category.Object D}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow (category-sum F) x y
      → Category.Arrow D x' y'
    map {x = ι₂ x₂} {y = ι₂ y₂} p₂ q₂ (CategorySum.arrow₁ f₁)
      = PartialFunctor.map G p₂ q₂ (WeakFunctor.map F' x₂ y₂ f₁)
    map p₂ q₂ (CategorySum.arrow₂ f₂)
      = PartialFunctor.map G p₂ q₂ f₂

    abstract

      map-identity
        : {x' : Category.Object D}
        → (x : Category.Object (category-sum F))
        → (p : base x ≡ just x')
        → map p p (Category.identity (category-sum F) x)
          ≡ Category.identity D x'
      map-identity (ι₂ x₂)
        = PartialFunctor.map-identity G x₂
  
      map-compose
        : {x y z : Category.Object (category-sum F)}
        → {x' y' z' : Category.Object D}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow (category-sum F) y z)
        → (g : Category.Arrow (category-sum F) x y)
        → map p r (Category.compose (category-sum F) f g)
          ≡ Category.compose D (map q r f) (map p q g)
      map-compose {x = ι₂ x₂} {y = ι₂ y₂} {z = ι₂ z₂} p₂ q₂ r₂
        (CategorySum.arrow₁ f₁) (CategorySum.arrow₁ g₁)
        with WeakFunctor.map F' x₂ z₂ (Category.compose C₁ f₁ g₁)
        | WeakFunctor.map-compose F' x₂ y₂ z₂ f₁ g₁
      ... | _ | refl
        = PartialFunctor.map-compose G p₂ q₂ r₂
          (WeakFunctor.map F' y₂ z₂ f₁)
          (WeakFunctor.map F' x₂ y₂ g₁)
      map-compose {x = ι₂ x₂} {y = ι₂ y₂} {z = ι₂ z₂} p₂ q₂ r₂
        (CategorySum.arrow₁ f₁) (CategorySum.arrow₂ g₂)
        with WeakFunctor.map F' x₂ z₂
          (Category.compose C₁ f₁ (Functor.map F g₂))
        | WeakFunctor.map-compose F' x₂ y₂ z₂ f₁ (Functor.map F g₂)
      ... | _ | refl
        with Category.compose C₂
          (WeakFunctor.map F' y₂ z₂ f₁)
          (WeakFunctor.map F' x₂ y₂ (Functor.map F g₂))
        | WeakFunctor.map-unmap₂ F' z₂ f₁ g₂
      ... | _ | refl
        = PartialFunctor.map-compose G p₂ q₂ r₂ (WeakFunctor.map F' y₂ z₂ f₁) g₂
      map-compose {x = ι₂ x₂} {y = ι₂ y₂} {z = ι₂ z₂} p₂ q₂ r₂
        (CategorySum.arrow₂ f₂) (CategorySum.arrow₁ g₁)
        with WeakFunctor.map F' x₂ z₂
          (Category.compose C₁ (Functor.map F f₂) g₁)
        | WeakFunctor.map-compose F' x₂ y₂ z₂ (Functor.map F f₂) g₁
      ... | _ | refl
        with Category.compose C₂
          (WeakFunctor.map F' y₂ z₂ (Functor.map F f₂))
          (WeakFunctor.map F' x₂ y₂ g₁)
        | WeakFunctor.map-unmap₁ F' x₂ f₂ g₁
      ... | _ | refl
        = PartialFunctor.map-compose G p₂ q₂ r₂ f₂ (WeakFunctor.map F' x₂ y₂ g₁)
      map-compose p₂ q₂ r₂ (CategorySum.arrow₂ f₂) (CategorySum.arrow₂ g₂)
        = PartialFunctor.map-compose G p₂ q₂ r₂ f₂ g₂

  partial-functor-sum₂
    : WeakFunctor F
    → PartialFunctor C₂ D
    → PartialFunctor (category-sum F) D
  partial-functor-sum₂ F' G
    = record {PartialFunctorSum₂ F' G}

-- ## PartialFunctorSquare₂

module _
  {C₁₁ C₁₂ C₂₁ C₂₂ D₁ D₂ : Category}
  {F₁ : Functor C₁₂ C₁₁}
  {F₂ : Functor C₂₂ C₂₁}
  {F₁' : WeakFunctor F₁}
  {F₂' : WeakFunctor F₂}
  {G₁ : Functor C₁₁ C₂₁}
  {G₂ : Functor C₁₂ C₂₂}
  {H : Functor D₁ D₂}
  {I₁ : PartialFunctor C₁₂ D₁}
  {I₂ : PartialFunctor C₂₂ D₂}
  {s : FunctorSquare G₂ G₁ F₁ F₂}
  where

  module PartialFunctorSquareSum₂
    (s' : WeakFunctorSquare F₁' F₂' s)
    (t : PartialFunctorSquare G₂ H I₁ I₂)
    where

    base
      : {x₁' : Category.Object D₁}
      → (x₁ : Category.Object (category-sum F₁))
      → PartialFunctor.base (partial-functor-sum₂ F₁' I₁) x₁ ≡ just x₁'
      → PartialFunctor.base
        (partial-functor-sum₂ F₂' I₂)
        (Functor.base (functor-sum s) x₁)
      ≡ just (Functor.base H x₁')
    base (ι₂ x₁₂)
      = PartialFunctorSquare.base t x₁₂

    map₁
      : (x₁₂ y₁₂ : Category.Object C₁₂)
      → (f₁₁ : Category.Arrow C₁₁ (Functor.base F₁ x₁₂) (Functor.base F₁ y₁₂))
      → WeakFunctor.map F₂'
        (Functor.base G₂ x₁₂)
        (Functor.base G₂ y₁₂)
        (Category.arrow C₂₁
          (FunctorSquare.base s x₁₂)
          (FunctorSquare.base s y₁₂)
          (Functor.map G₁ f₁₁))
      ≡ Functor.map G₂
        (WeakFunctor.map F₁' x₁₂ y₁₂ f₁₁)
    map₁ x₁₂ y₁₂ f₁₁
      = trans
        (sym (WeakFunctor.map-eq' F₂'
          (Functor.base G₂ x₁₂)
          (Functor.base G₂ y₁₂)
          (FunctorSquare.base s x₁₂)
          (FunctorSquare.base s y₁₂)
          (Category.arrow-eq C₂₁
            (FunctorSquare.base s x₁₂)
            (FunctorSquare.base s y₁₂)
            (Functor.map G₁ f₁₁))))
        (WeakFunctorSquare.map s' x₁₂ y₁₂ f₁₁)

    map
      : {x₁ y₁ : Category.Object (category-sum F₁)}
      → {x₁' y₁' : Category.Object D₁}
      → (p₁ : PartialFunctor.base (partial-functor-sum₂ F₁' I₁) x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-sum₂ F₁' I₁) y₁ ≡ just y₁')
      → (f₁ : Category.Arrow (category-sum F₁) x₁ y₁)
      → PartialFunctor.map
        (partial-functor-sum₂ F₂' I₂)
        (base x₁ p₁)
        (base y₁ q₁)
        (Functor.map (functor-sum s) f₁)
      ≡ Functor.map H
        (PartialFunctor.map (partial-functor-sum₂ F₁' I₁) p₁ q₁ f₁)
    map {x₁ = ι₂ x₁₂} {y₁ = ι₂ y₁₂} p₁ q₁ (CategorySum.arrow₁ f₁₁)
      = trans
        (sub
          (PartialFunctor.map I₂
            (PartialFunctorSquare.base t x₁₂ p₁)
            (PartialFunctorSquare.base t y₁₂ q₁))
          (map₁ x₁₂ y₁₂ f₁₁))
        (PartialFunctorSquare.map t p₁ q₁
          (WeakFunctor.map F₁' x₁₂ y₁₂ f₁₁))
    map p₁ q₁ (CategorySum.arrow₂ f₂)
      = PartialFunctorSquare.map t p₁ q₁ f₂

  partial-functor-square-sum₂
    : WeakFunctorSquare F₁' F₂' s
    → (t : PartialFunctorSquare G₂ H I₁ I₂)
    → PartialFunctorSquare
      (functor-sum s) H
      (partial-functor-sum₂ F₁' I₁)
      (partial-functor-sum₂ F₂' I₂)
  partial-functor-square-sum₂ s' t
    = record {PartialFunctorSquareSum₂ s' t}
  
