module Prover.Category.Partial.Unit where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Unit
  using (module CategoryUnit; category-unit; functor-unit)
open import Prover.Function
  using (Function)
open import Prover.Function.Partial
  using (PartialFunction; PartialFunctionSquare)
open import Prover.Prelude

-- ## PartialFunctor

module _
  {A B : Set}
  where

  module PartialFunctorUnit
    (F : PartialFunction A B)
    where

    open PartialFunction F public
      using (base)

    map
      : {x y : Category.Object (category-unit A)}
      → {x' y' : Category.Object (category-unit B)}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow (category-unit A) x y
      → Category.Arrow (category-unit B) x' y'
    map _ _ _
      = CategoryUnit.arrow

    abstract

      map-identity
        : {x' : Category.Object (category-unit B)}
        → (x : Category.Object (category-unit A))
        → (p : base x ≡ just x')
        → map p p (Category.identity (category-unit A) x)
          ≡ Category.identity (category-unit B) x'
      map-identity _ _
        = refl
  
      map-compose
        : {x y z : Category.Object (category-unit A)}
        → {x' y' z' : Category.Object (category-unit B)}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow (category-unit A) y z)
        → (g : Category.Arrow (category-unit A) x y)
        → map p r (Category.compose (category-unit A) f g)
          ≡ Category.compose (category-unit B) (map q r f) (map p q g)
      map-compose _ _ _ _ _
        = refl

  partial-functor-unit
    : PartialFunction A B
    → PartialFunctor
      (category-unit A)
      (category-unit B)
  partial-functor-unit F
    = record {PartialFunctorUnit F}

-- ## PartialFunctorSquare

module _
  {A₁ A₂ B₁ B₂ : Set}
  {F : Function A₁ A₂}
  {G : Function B₁ B₂}
  {H₁ : PartialFunction A₁ B₁}
  {H₂ : PartialFunction A₂ B₂}
  where

  module PartialFunctorSquareUnit
    (s : PartialFunctionSquare F G H₁ H₂)
    where

    open PartialFunctionSquare s public
      using (base)

    map
      : {x₁ y₁ : Category.Object (category-unit A₁)}
      → {x₁' y₁' : Category.Object (category-unit B₁)}
      → (p₁ : PartialFunctor.base (partial-functor-unit H₁) x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-unit H₁) y₁ ≡ just y₁')
      → (f₁ : Category.Arrow (category-unit A₁) x₁ y₁)
      → PartialFunctor.map (partial-functor-unit H₂) (base x₁ p₁) (base y₁ q₁)
        (Functor.map (functor-unit F) f₁)
      ≡ Functor.map (functor-unit G)
        (PartialFunctor.map (partial-functor-unit H₁) p₁ q₁ f₁)
    map _ _ _
      = refl

  partial-functor-square-unit
    : PartialFunctionSquare F G H₁ H₂
    → PartialFunctorSquare
      (functor-unit F)
      (functor-unit G)
      (partial-functor-unit H₁)
      (partial-functor-unit H₂)
  partial-functor-square-unit s
    = record {PartialFunctorSquareUnit s}

