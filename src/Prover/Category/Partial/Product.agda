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

    map-identity
      : {x' : Category.Object (category-product D₁ D₂)}
      → (x : Category.Object (category-product C₁ C₂))
      → (p : base x ≡ just x')
      → map p p (Category.identity (category-product C₁ C₂) x)
        ≡ Category.identity (category-product D₁ D₂) x'
    map-identity (x₁ , x₂) _
      with PartialFunctor.base F₁ x₁
      | inspect (PartialFunctor.base F₁) x₁
      | PartialFunctor.base F₂ x₂
      | inspect (PartialFunctor.base F₂) x₂
    map-identity (x₁ , x₂) refl | just _ | [ p₁ ] | just _ | [ p₂ ]
      = Sigma.comma-eq
        (PartialFunctor.map-identity F₁ x₁ p₁)
        (PartialFunctor.map-identity F₂ x₂ p₂)

    map-compose
      : {x y z : Category.Object (category-product C₁ C₂)}
      → {x' y' z' : Category.Object (category-product D₁ D₂)}
      → (p : base x ≡ just x')
      → (q : base y ≡ just y')
      → (r : base z ≡ just z')
      → (f : Category.Arrow (category-product C₁ C₂) y z)
      → (g : Category.Arrow (category-product C₁ C₂) x y)
      → map p r (Category.compose (category-product C₁ C₂) f g)
        ≡ Category.compose (category-product D₁ D₂) (map q r f) (map p q g)
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
      = Sigma.comma-eq
        (PartialFunctor.map-compose F₁ p₁ q₁ r₁ f₁ g₁)
        (PartialFunctor.map-compose F₂ p₂ q₂ r₂ f₂ g₂)

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
  {F₁ : Functor C₁₁ C₂₁}
  {F₂ : Functor C₁₂ C₂₂}
  {G₁ : Functor D₁₁ D₂₁}
  {G₂ : Functor D₁₂ D₂₂}
  {H₁₁ : PartialFunctor C₁₁ D₁₁}
  {H₁₂ : PartialFunctor C₁₂ D₁₂}
  {H₂₁ : PartialFunctor C₂₁ D₂₁}
  {H₂₂ : PartialFunctor C₂₂ D₂₂}
  where

  module PartialFunctorSquareProduct
    (s₁ : PartialFunctorSquare F₁ G₁ H₁₁ H₂₁)
    (s₂ : PartialFunctorSquare F₂ G₂ H₁₂ H₂₂)
    where

    base
      : {x₁' : Category.Object (category-product D₁₁ D₁₂)}
      → (x₁ : Category.Object (category-product C₁₁ C₁₂))
      → PartialFunctor.base (partial-functor-product H₁₁ H₁₂) x₁ ≡ just x₁'
      → PartialFunctor.base (partial-functor-product H₂₁ H₂₂)
        (Functor.base (functor-product F₁ F₂) x₁)
      ≡ just (Functor.base (functor-product G₁ G₂) x₁')
    base (x₁₁ , x₁₂) _
      with PartialFunctor.base H₁₁ x₁₁
      | inspect (PartialFunctor.base H₁₁) x₁₁
      | PartialFunctor.base H₁₂ x₁₂
      | inspect (PartialFunctor.base H₁₂) x₁₂
    base (x₁₁ , x₁₂) refl | just _ | [ p₁ ] | just _ | [ p₂ ]
      with PartialFunctor.base H₂₁ (Functor.base F₁ x₁₁)
      | PartialFunctorSquare.base s₁ x₁₁ p₁
      | PartialFunctor.base H₂₂ (Functor.base F₂ x₁₂)
      | PartialFunctorSquare.base s₂ x₁₂ p₂
    ... | _ | refl | _ | refl
      = refl

    map
      : {x₁ y₁ : Category.Object (category-product C₁₁ C₁₂)}
      → {x₁' y₁' : Category.Object (category-product D₁₁ D₁₂)}
      → (p₁ : PartialFunctor.base (partial-functor-product H₁₁ H₁₂) x₁
        ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-product H₁₁ H₁₂) y₁
        ≡ just y₁')
      → (f₁ : Category.Arrow (category-product C₁₁ C₁₂) x₁ y₁)
      → PartialFunctor.map
        (partial-functor-product H₂₁ H₂₂)
        (base x₁ p₁)
        (base y₁ q₁)
        (Functor.map (functor-product F₁ F₂) f₁)
      ≡ Functor.map (functor-product G₁ G₂)
        (PartialFunctor.map (partial-functor-product H₁₁ H₁₂) p₁ q₁ f₁)
    map {x₁ = (x₁₁ , x₁₂)} {y₁ = (y₁₁ , y₁₂)} _ _ _
      with PartialFunctor.base H₁₁ x₁₁
      | inspect (PartialFunctor.base H₁₁) x₁₁
      | PartialFunctor.base H₁₂ x₁₂
      | inspect (PartialFunctor.base H₁₂) x₁₂
      | PartialFunctor.base H₁₁ y₁₁
      | inspect (PartialFunctor.base H₁₁) y₁₁
      | PartialFunctor.base H₁₂ y₁₂
      | inspect (PartialFunctor.base H₁₂) y₁₂
    map {x₁ = (x₁₁ , x₁₂)} {y₁ = (y₁₁ , y₁₂)} refl refl (f₁₁ , f₁₂)
      | just _ | [ p₁₁ ] | just _ | [ p₁₂ ]
      | just _ | [ q₁₁ ] | just _ | [ q₁₂ ]
      with PartialFunctor.base H₂₁ (Functor.base F₁ x₁₁)
      | inspect (PartialFunctor.base H₂₁) (Functor.base F₁ x₁₁)
      | PartialFunctorSquare.base s₁ x₁₁ p₁₁
      | PartialFunctor.base H₂₂ (Functor.base F₂ x₁₂)
      | inspect (PartialFunctor.base H₂₂) (Functor.base F₂ x₁₂)
      | PartialFunctorSquare.base s₂ x₁₂ p₁₂
      | PartialFunctor.base H₂₁ (Functor.base F₁ y₁₁)
      | inspect (PartialFunctor.base H₂₁) (Functor.base F₁ y₁₁)
      | PartialFunctorSquare.base s₁ y₁₁ q₁₁
      | PartialFunctor.base H₂₂ (Functor.base F₂ y₁₂)
      | inspect (PartialFunctor.base H₂₂) (Functor.base F₂ y₁₂)
      | PartialFunctorSquare.base s₂ y₁₂ q₁₂
    ... | just _ | [ p₂₁ ] | refl | just _ | [ p₂₂ ] | refl
      | just _ | [ q₂₁ ] | refl | just _ | [ q₂₂ ] | refl
      with PartialFunctor.map H₂₁ p₂₁ q₂₁ (Functor.map F₁ f₁₁)
      | PartialFunctorSquare.map-eq s₁ p₁₁ q₁₁ p₂₁ q₂₁ f₁₁
      | PartialFunctor.map H₂₂ p₂₂ q₂₂ (Functor.map F₂ f₁₂)
      | PartialFunctorSquare.map-eq s₂ p₁₂ q₁₂ p₂₂ q₂₂ f₁₂
    ... | _ | refl | _ | refl
      = refl

  partial-functor-square-product
    : PartialFunctorSquare F₁ G₁ H₁₁ H₂₁
    → PartialFunctorSquare F₂ G₂ H₁₂ H₂₂
    → PartialFunctorSquare
      (functor-product F₁ F₂)
      (functor-product G₁ G₂)
      (partial-functor-product H₁₁ H₁₂)
      (partial-functor-product H₂₁ H₂₂)
  partial-functor-square-product s₁ s₂
    = record {PartialFunctorSquareProduct s₁ s₂}

