module Prover.Category.Partial.Product where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Product
  using (category-product; functor-product)
open import Prover.Prelude

-- ## PartialFunctor

module _
  {C₁ C₂ D₁ D₂ : Category}
  where

  module PartialFunctorProduct
    (F₁ : PartialFunctor C₁ D₁)
    (F₂ : PartialFunctor C₂ D₂)
    where

    base
      : Category.Object (category-product C₁ C₂)
      → Maybe (Category.Object (category-product D₁ D₂))
    base (x₁ , x₂)
      with PartialFunctor.base F₁ x₁
      | PartialFunctor.base F₂ x₂
    ... | nothing | _
      = nothing
    ... | _ | nothing
      = nothing
    ... | just x₁' | just x₂'
      = just (x₁' , x₂')

    map
      : {x y : Category.Object (category-product C₁ C₂)}
      → {x' y' : Category.Object (category-product D₁ D₂)}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow (category-product C₁ C₂) x y
      → Category.Arrow (category-product D₁ D₂) x' y'
    map {x = (x₁ , x₂)} {y = (y₁ , y₂)} _ _ _
      with PartialFunctor.base F₁ x₁
      | inspect (PartialFunctor.base F₁) x₁
      | PartialFunctor.base F₂ x₂
      | inspect (PartialFunctor.base F₂) x₂
      | PartialFunctor.base F₁ y₁
      | inspect (PartialFunctor.base F₁) y₁
      | PartialFunctor.base F₂ y₂
      | inspect (PartialFunctor.base F₂) y₂
    map refl refl (f₁ , f₂)
      | just _ | [ p₁ ] | just _ | [ p₂ ]
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      = PartialFunctor.map F₁ p₁ q₁ f₁
      , PartialFunctor.map F₂ p₂ q₂ f₂

    abstract

      map-equal
        : {x y : Category.Object (category-product C₁ C₂)}
        → {x' y' : Category.Object (category-product D₁ D₂)}
        → {f₁ f₂ : Category.Arrow (category-product C₁ C₂) x y}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → Category.ArrowEqual (category-product C₁ C₂) f₁ f₂
        → Category.ArrowEqual (category-product D₁ D₂) (map p q f₁) (map p q f₂)
      map-equal {x = (x₁ , x₂)} {y = (y₁ , y₂)} _ _ _
        with PartialFunctor.base F₁ x₁
        | inspect (PartialFunctor.base F₁) x₁
        | PartialFunctor.base F₂ x₂
        | inspect (PartialFunctor.base F₂) x₂
        | PartialFunctor.base F₁ y₁
        | inspect (PartialFunctor.base F₁) y₁
        | PartialFunctor.base F₂ y₂
        | inspect (PartialFunctor.base F₂) y₂
      map-equal refl refl (r₁ , r₂)
        | just _ | [ p₁ ] | just _ | [ p₂ ]
        | just _ | [ q₁ ] | just _ | [ q₂ ]
        = PartialFunctor.map-equal F₁ p₁ q₁ r₁
        , PartialFunctor.map-equal F₂ p₂ q₂ r₂

      map-identity
        : {x' : Category.Object (category-product D₁ D₂)}
        → (x : Category.Object (category-product C₁ C₂))
        → (p : base x ≡ just x')
        → Category.ArrowEqual (category-product D₁ D₂)
          (map p p (Category.identity (category-product C₁ C₂) x))
          (Category.identity (category-product D₁ D₂) x')
      map-identity (x₁ , x₂) _
        with PartialFunctor.base F₁ x₁
        | inspect (PartialFunctor.base F₁) x₁
        | PartialFunctor.base F₂ x₂
        | inspect (PartialFunctor.base F₂) x₂
      map-identity (x₁ , x₂) refl
        | just _ | [ p₁ ] | just _ | [ p₂ ]
        = PartialFunctor.map-identity F₁ x₁ p₁
        , PartialFunctor.map-identity F₂ x₂ p₂
  
      map-compose
        : {x y z : Category.Object (category-product C₁ C₂)}
        → {x' y' z' : Category.Object (category-product D₁ D₂)}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow (category-product C₁ C₂) y z)
        → (g : Category.Arrow (category-product C₁ C₂) x y)
        → Category.ArrowEqual (category-product D₁ D₂)
          (map p r (Category.compose (category-product C₁ C₂) f g))
          (Category.compose (category-product D₁ D₂) (map q r f) (map p q g))
      map-compose {x = (x₁ , x₂)} {y = (y₁ , y₂)} {z = (z₁ , z₂)} _ _ _ _ _
        with PartialFunctor.base F₁ x₁
        | inspect (PartialFunctor.base F₁) x₁
        | PartialFunctor.base F₂ x₂
        | inspect (PartialFunctor.base F₂) x₂
        | PartialFunctor.base F₁ y₁
        | inspect (PartialFunctor.base F₁) y₁
        | PartialFunctor.base F₂ y₂
        | inspect (PartialFunctor.base F₂) y₂
        | PartialFunctor.base F₁ z₁
        | inspect (PartialFunctor.base F₁) z₁
        | PartialFunctor.base F₂ z₂
        | inspect (PartialFunctor.base F₂) z₂
      map-compose refl refl refl (f₁ , f₂) (g₁ , g₂)
        | just _ | [ p₁ ] | just _ | [ p₂ ]
        | just _ | [ q₁ ] | just _ | [ q₂ ]
        | just _ | [ r₁ ] | just _ | [ r₂ ]
        = PartialFunctor.map-compose F₁ p₁ q₁ r₁ f₁ g₁
        , PartialFunctor.map-compose F₂ p₂ q₂ r₂ f₂ g₂

  partial-functor-product
    : PartialFunctor C₁ D₁
    → PartialFunctor C₂ D₂
    → PartialFunctor
      (category-product C₁ C₂)
      (category-product D₁ D₂)
  partial-functor-product F₁ F₂
    = record {PartialFunctorProduct F₁ F₂}

-- ## PartialFunctorSquare

module _
  {C₁₁ C₁₂ C₂₁ C₂₂ D₁₁ D₁₂ D₂₁ D₂₂ : Category}
  {F₁ : Functor C₁₁ C₁₂}
  {F₂ : Functor C₂₁ C₂₂}
  {G₁ : Functor D₁₁ D₁₂}
  {G₂ : Functor D₂₁ D₂₂}
  {H₁₁ : PartialFunctor C₁₁ D₁₁}
  {H₁₂ : PartialFunctor C₁₂ D₁₂}
  {H₂₁ : PartialFunctor C₂₁ D₂₁}
  {H₂₂ : PartialFunctor C₂₂ D₂₂}
  where

  module PartialFunctorSquareProduct
    (s₁ : PartialFunctorSquare F₁ G₁ H₁₁ H₁₂)
    (s₂ : PartialFunctorSquare F₂ G₂ H₂₁ H₂₂)
    where

    base
      : {x₁' : Category.Object (category-product D₁₁ D₂₁)}
      → (x₁ : Category.Object (category-product C₁₁ C₂₁))
      → PartialFunctor.base (partial-functor-product H₁₁ H₂₁) x₁ ≡ just x₁'
      → PartialFunctor.base (partial-functor-product H₁₂ H₂₂)
        (Functor.base (functor-product F₁ F₂) x₁)
      ≡ just (Functor.base (functor-product G₁ G₂) x₁')
    base (x₁₁ , x₂₁) _
      with PartialFunctor.base H₁₁ x₁₁
      | inspect (PartialFunctor.base H₁₁) x₁₁
      | PartialFunctor.base H₂₁ x₂₁
      | inspect (PartialFunctor.base H₂₁) x₂₁
    base (x₁₁ , x₂₁) refl
      | just _ | [ p₁ ] | just _ | [ p₂ ]
      with PartialFunctor.base H₁₂ (Functor.base F₁ x₁₁)
      | PartialFunctorSquare.base s₁ x₁₁ p₁
      | PartialFunctor.base H₂₂ (Functor.base F₂ x₂₁)
      | PartialFunctorSquare.base s₂ x₂₁ p₂
    ... | _ | refl | _ | refl
      = refl

    map
      : {x₁ y₁ : Category.Object (category-product C₁₁ C₂₁)}
      → {x₁' y₁' : Category.Object (category-product D₁₁ D₂₁)}
      → (p₁ : PartialFunctor.base (partial-functor-product H₁₁ H₂₁) x₁
        ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-product H₁₁ H₂₁) y₁
        ≡ just y₁')
      → (f₁ : Category.Arrow (category-product C₁₁ C₂₁) x₁ y₁)
      → Category.ArrowEqual (category-product D₁₂ D₂₂)
        (PartialFunctor.map
          (partial-functor-product H₁₂ H₂₂)
          (base x₁ p₁)
          (base y₁ q₁)
          (Functor.map (functor-product F₁ F₂) f₁))
        (Functor.map (functor-product G₁ G₂)
          (PartialFunctor.map (partial-functor-product H₁₁ H₂₁) p₁ q₁ f₁))
    map {x₁ = (x₁₁ , x₂₁)} {y₁ = (y₁₁ , y₂₁)} _ _ _
      with PartialFunctor.base H₁₁ x₁₁
      | inspect (PartialFunctor.base H₁₁) x₁₁
      | PartialFunctor.base H₂₁ x₂₁
      | inspect (PartialFunctor.base H₂₁) x₂₁
      | PartialFunctor.base H₁₁ y₁₁
      | inspect (PartialFunctor.base H₁₁) y₁₁
      | PartialFunctor.base H₂₁ y₂₁
      | inspect (PartialFunctor.base H₂₁) y₂₁
    map {x₁ = (x₁₁ , x₂₁)} {y₁ = (y₁₁ , y₂₁)} refl refl (f₁₁ , f₂₁)
      | just _ | [ p₁₁ ] | just _ | [ p₂₁ ]
      | just _ | [ q₁₁ ] | just _ | [ q₂₁ ]
      with PartialFunctor.base H₁₂ (Functor.base F₁ x₁₁)
      | inspect (PartialFunctor.base H₁₂) (Functor.base F₁ x₁₁)
      | PartialFunctorSquare.base s₁ x₁₁ p₁₁
      | PartialFunctor.base H₂₂ (Functor.base F₂ x₂₁)
      | inspect (PartialFunctor.base H₂₂) (Functor.base F₂ x₂₁)
      | PartialFunctorSquare.base s₂ x₂₁ p₂₁
      | PartialFunctor.base H₁₂ (Functor.base F₁ y₁₁)
      | inspect (PartialFunctor.base H₁₂) (Functor.base F₁ y₁₁)
      | PartialFunctorSquare.base s₁ y₁₁ q₁₁
      | PartialFunctor.base H₂₂ (Functor.base F₂ y₂₁)
      | inspect (PartialFunctor.base H₂₂) (Functor.base F₂ y₂₁)
      | PartialFunctorSquare.base s₂ y₂₁ q₂₁
    ... | just _ | [ p₁₂ ] | refl | just _ | [ p₂₂ ] | refl
      | just _ | [ q₁₂ ] | refl | just _ | [ q₂₂ ] | refl
      = PartialFunctorSquare.map' s₁ p₁₁ q₁₁ p₁₂ q₁₂ f₁₁
      , PartialFunctorSquare.map' s₂ p₂₁ q₂₁ p₂₂ q₂₂ f₂₁

  partial-functor-square-product
    : PartialFunctorSquare F₁ G₁ H₁₁ H₁₂
    → PartialFunctorSquare F₂ G₂ H₂₁ H₂₂
    → PartialFunctorSquare
      (functor-product F₁ F₂)
      (functor-product G₁ G₂)
      (partial-functor-product H₁₁ H₂₁)
      (partial-functor-product H₁₂ H₂₂)
  partial-functor-square-product s₁ s₂
    = record {PartialFunctorSquareProduct s₁ s₂}

