module Prover.Category.Partial.Maybe where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Maybe
  using (category-maybe; functor-maybe)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Prelude

-- ## PartialFunctor

module _
  {C D : Category}
  where

  module PartialFunctorMaybe
    (F : PartialFunctor C D)
    where
  
    open PartialFunctor F
      using (base)

    map
      : {x y : Category.Object (category-maybe C)}
      → {x' y' : Category.Object (category-maybe D)}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow (category-maybe C) x y
      → Category.Arrow (category-maybe D) x' y'
    map p q
      = Maybe.map (PartialFunctor.map F p q)

    abstract

      map-identity
        : {x' : Category.Object (category-maybe D)}
        → (x : Category.Object (category-maybe C))
        → (p : base x ≡ just x')
        → map p p (Category.identity (category-maybe C) x)
          ≡ Category.identity (category-maybe D) x'
      map-identity x p
        = sub just (PartialFunctor.map-identity F x p)
  
      map-compose
        : {x y z : Category.Object (category-maybe C)}
        → {x' y' z' : Category.Object (category-maybe D)}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow (category-maybe C) y z)
        → (g : Category.Arrow (category-maybe C) x y)
        → map p r (Category.compose (category-maybe C) f g)
          ≡ Category.compose (category-maybe D) (map q r f) (map p q g)
      map-compose _ _ _ nothing _
        = refl
      map-compose _ _ _ (just _) nothing
        = refl
      map-compose p q r (just f) (just g)
        = sub just (PartialFunctor.map-compose F p q r f g)

  partial-functor-maybe
    : PartialFunctor C D
    → PartialFunctor
      (category-maybe C)
      (category-maybe D)
  partial-functor-maybe F
    = record {PartialFunctorMaybe F}

-- ## PartialFunctorSquare

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : PartialFunctor C₁ D₁}
  {H₂ : PartialFunctor C₂ D₂}
  where

  module PartialFunctorSquareMaybe
    (s : PartialFunctorSquare F G H₁ H₂)
    where

    base
      : {x₁' : Category.Object (category-maybe D₁)}
      → (x₁ : Category.Object (category-maybe C₁))
      → PartialFunctor.base (partial-functor-maybe H₁) x₁ ≡ just x₁'
      → PartialFunctor.base (partial-functor-maybe H₂)
        (Functor.base (functor-maybe F) x₁)
      ≡ just (Functor.base (functor-maybe G) x₁')
    base
      = PartialFunctorSquare.base s

    map
      : {x₁ y₁ : Category.Object (category-maybe C₁)}
      → {x₁' y₁' : Category.Object (category-maybe D₁)}
      → (p₁ : PartialFunctor.base (partial-functor-maybe H₁) x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-maybe H₁) y₁ ≡ just y₁')
      → (f₁ : Category.Arrow (category-maybe C₁) x₁ y₁)
      → PartialFunctor.map (partial-functor-maybe H₂)
        (base x₁ p₁)
        (base y₁ q₁)
        (Functor.map (functor-maybe F) f₁)
      ≡ Functor.map (functor-maybe G)
        (PartialFunctor.map (partial-functor-maybe H₁) p₁ q₁ f₁)
    map _ _ nothing
      = refl
    map p₁ q₁ (just f₁)
      = sub just (PartialFunctorSquare.map s p₁ q₁ f₁)

  partial-functor-square-maybe
    : PartialFunctorSquare F G H₁ H₂
    → PartialFunctorSquare
      (functor-maybe F)
      (functor-maybe G)
      (partial-functor-maybe H₁)
      (partial-functor-maybe H₂)
  partial-functor-square-maybe s
    = record {PartialFunctorSquareMaybe s}

