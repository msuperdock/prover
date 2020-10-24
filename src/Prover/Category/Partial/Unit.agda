module Prover.Category.Partial.Unit where

open import Prover.Category
  using (Category)
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

      map-equal
        : {x y : Category.Object (category-unit A)}
        → {x' y' : Category.Object (category-unit B)}
        → {f₁ f₂ : Category.Arrow (category-unit A) x y}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → Category.ArrowEqual (category-unit A) f₁ f₂
        → Category.ArrowEqual (category-unit B) (map p q f₁) (map p q f₂)
      map-equal _ _ _
        = refl

      map-identity
        : {x' : Category.Object (category-unit B)}
        → (x : Category.Object (category-unit A))
        → (p : base x ≡ just x')
        → Category.ArrowEqual (category-unit B)
          (map p p (Category.identity (category-unit A) x))
          (Category.identity (category-unit B) x')
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
        → Category.ArrowEqual (category-unit B)
          (map p r (Category.compose (category-unit A) f g))
          (Category.compose (category-unit B) (map q r f) (map p q g))
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

partial-functor-square-unit
  : {A₁ A₂ B₁ B₂ : Set}
  → {F : Function A₁ A₂}
  → {G : Function B₁ B₂}
  → {H₁ : PartialFunction A₁ B₁}
  → {H₂ : PartialFunction A₂ B₂}
  → PartialFunctionSquare F G H₁ H₂
  → PartialFunctorSquare
    (functor-unit F)
    (functor-unit G)
    (partial-functor-unit H₁)
    (partial-functor-unit H₂)
partial-functor-square-unit s
  = record
  { PartialFunctionSquare s
  ; map
    = λ _ _ _ → refl
  }

