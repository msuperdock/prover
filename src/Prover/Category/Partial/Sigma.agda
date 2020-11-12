module Prover.Category.Partial.Sigma where

open import Prover.Category
  using (Category; Functor; any; any')
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Dependent1.Partial
  using (Dependent₁PartialFunctor; Dependent₁PartialFunctorSquare)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Sigma
  using (module CategorySigma; arrow-equal-sigma; category-sigma; functor-sigma)
open import Prover.Prelude

-- ## PartialFunctor

module _
  {C₁ : Category}
  {C₂ D₂ : Dependent₁Category C₁}
  where

  module PartialFunctorSigma
    (F₂ : Dependent₁PartialFunctor C₂ D₂)
    where

    base
      : Category.Object (category-sigma C₂)
      → Maybe (Category.Object (category-sigma D₂))
    base (x₁ , x₂)
      with Dependent₁PartialFunctor.base F₂ x₁ x₂
    ... | nothing
      = nothing
    ... | just x₂'
      = just (x₁ , x₂')

    map
      : {x y : Category.Object (category-sigma C₂)}
      → {x' y' : Category.Object (category-sigma D₂)}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow (category-sigma C₂) x y
      → Category.Arrow (category-sigma D₂) x' y'
    map {x = (x₁ , x₂)} {y = (y₁ , y₂)} _ _ _
      with Dependent₁PartialFunctor.base F₂ x₁ x₂
      | inspect (Dependent₁PartialFunctor.base F₂ x₁) x₂
      | Dependent₁PartialFunctor.base F₂ y₁ y₂
      | inspect (Dependent₁PartialFunctor.base F₂ y₁) y₂
    map {x = (_ , x₂)} {y = (y₁ , _)} refl refl
      (CategorySigma.arrow f₁ f₂ p₂)
      | just _ | [ q₂ ] | just _ | [ r₂ ]
      = record
      { arrow₁
        = f₁
      ; arrow₂
        = Dependent₁PartialFunctor.map F₂ y₁
          (trans (sub (Dependent₁PartialFunctor.base F₂ y₁) (sym p₂))
            (Dependent₁PartialFunctor.base-square F₂ f₁ x₂ q₂)) r₂ f₂
      ; valid
        = refl
      }

    abstract

      map-equal
        : {x y : Category.Object (category-sigma C₂)}
        → {x' y' : Category.Object (category-sigma D₂)}
        → {f₁ f₂ : Category.Arrow (category-sigma C₂) x y}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → Category.ArrowEqual (category-sigma C₂) f₁ f₂
        → Category.ArrowEqual (category-sigma D₂) (map p q f₁) (map p q f₂)
      map-equal {x = (x₁ , x₂)} {y = (y₁ , y₂)} _ _ _
        with Dependent₁PartialFunctor.base F₂ x₁ x₂
        | inspect (Dependent₁PartialFunctor.base F₂ x₁) x₂
        | Dependent₁PartialFunctor.base F₂ y₁ y₂
        | inspect (Dependent₁PartialFunctor.base F₂ y₁) y₂
      map-equal {x = (_ , x₂)} {y = (y₁ , _)}
        {f₁ = CategorySigma.arrow f₁₁ _ refl}
        {f₂ = CategorySigma.arrow f₁₂ _ refl} refl refl
        (CategorySigma.arrow-equal p₁ p₂)
        | just _ | [ q₂ ] | just _ | [ r₂ ]
        = record
        { arrow₁
          = p₁
        ; arrow₂
          = Dependent₁PartialFunctor.map-equal' F₂ y₁
            (Dependent₁PartialFunctor.base-square F₂ f₁₁ x₂ q₂)
            (Dependent₁PartialFunctor.base-square F₂ f₁₂ x₂ q₂) r₂ r₂ p₂
        }

      map-identity
        : {x' : Category.Object (category-sigma D₂)}
        → (x : Category.Object (category-sigma C₂))
        → (p : base x ≡ just x')
        → Category.ArrowEqual
          (category-sigma D₂)
          (map p p (Category.identity (category-sigma C₂) x))
          (Category.identity (category-sigma D₂) x')
      map-identity (x₁ , x₂) _
        with Dependent₁PartialFunctor.base F₂ x₁ x₂
        | inspect (Dependent₁PartialFunctor.base F₂ x₁) x₂
      map-identity (x₁ , x₂) refl
        | just _ | [ p₂ ]
        = record
        { arrow₁
          = Category.arrow-refl C₁
        ; arrow₂
          = Dependent₁PartialFunctor.map-identity' F₂ x₁ x₂ p₂' p₂
        }
        where
          p₂' = trans
            (sub (Dependent₁PartialFunctor.base F₂ x₁)
              (sym (Dependent₁Category.base-identity C₂ x₁ x₂)))
            (Dependent₁PartialFunctor.base-square F₂
              (Category.identity C₁ x₁) x₂ p₂)
  
      map-compose
        : {x y z : Category.Object (category-sigma C₂)}
        → {x' y' z' : Category.Object (category-sigma D₂)}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow (category-sigma C₂) y z)
        → (g : Category.Arrow (category-sigma C₂) x y)
        → Category.ArrowEqual
          (category-sigma D₂)
          (map p r (Category.compose (category-sigma C₂) f g))
          (Category.compose (category-sigma D₂) (map q r f) (map p q g))
      map-compose {x = (x₁ , x₂)} {y = (y₁ , y₂)} {z = (z₁ , z₂)} _ _ _ _ _
        with Dependent₁PartialFunctor.base F₂ x₁ x₂
        | inspect (Dependent₁PartialFunctor.base F₂ x₁) x₂
        | Dependent₁PartialFunctor.base F₂ y₁ y₂
        | inspect (Dependent₁PartialFunctor.base F₂ y₁) y₂
        | Dependent₁PartialFunctor.base F₂ z₁ z₂
        | inspect (Dependent₁PartialFunctor.base F₂ z₁) z₂
      map-compose {x = (_ , x₂)} {y = (y₁ , y₂)} {z = (z₁ , _)} refl refl refl
        (CategorySigma.arrow f₁ f₂ refl)
        (CategorySigma.arrow g₁ g₂ refl)
        | just _ | [ p₂ ] | just _ | [ q₂ ] | just _ | [ r₂ ]
        = record
        { arrow₁
          = Category.arrow-refl C₁
        ; arrow₂
          = Dependent₁Category.arrow-trans' D₂ z₁
            (Dependent₁PartialFunctor.map-compose' F₂ z₁ p₂'' q₂' r₂ f₂
              (Dependent₁Category.map C₂ f₁ g₂))
          $ Dependent₁Category.compose-equal' D₂ z₁
            (Dependent₁PartialFunctor.map-equal' F₂ z₁ q₂' q₂' r₂ r₂
              (Dependent₁Category.arrow-refl' C₂ z₁))
            (Dependent₁PartialFunctor.map-square'' F₂ f₁ p₂' q₂ p₂'' q₂' g₂
              (Dependent₁Category.arrow-refl' C₂ z₁))
        }
        where
          p₂' = Dependent₁PartialFunctor.base-square F₂ g₁ x₂ p₂
          q₂' = Dependent₁PartialFunctor.base-square F₂ f₁ y₂ q₂
          p₂'' = trans
            (sub (Dependent₁PartialFunctor.base F₂ z₁)
              (sym (trans (Dependent₁Category.base-compose C₂ f₁ g₁ x₂) refl)))
            (Dependent₁PartialFunctor.base-square F₂
              (Category.compose C₁ f₁ g₁) x₂ p₂)

  partial-functor-sigma
    : Dependent₁PartialFunctor C₂ D₂
    → PartialFunctor
      (category-sigma C₂)
      (category-sigma D₂)
  partial-functor-sigma F₂
    = record {PartialFunctorSigma F₂}

-- ## PartialFunctorSquare

module _
  {C₁₁ C₁₂ : Category}
  {C₂₁ D₂₁ : Dependent₁Category C₁₁}
  {C₂₂ D₂₂ : Dependent₁Category C₁₂}
  {F₁ : Functor C₁₁ C₁₂}
  {F₂ : Dependent₁Functor C₂₁ C₂₂ F₁}
  {G₂ : Dependent₁Functor D₂₁ D₂₂ F₁}
  {H₂₁ : Dependent₁PartialFunctor C₂₁ D₂₁}
  {H₂₂ : Dependent₁PartialFunctor C₂₂ D₂₂}
  where

  module PartialFunctorSquareSigma
    (s : Dependent₁PartialFunctorSquare F₂ G₂ H₂₁ H₂₂)
    where

    base
      : {x₁' : Category.Object (category-sigma D₂₁)}
      → (x₁ : Category.Object (category-sigma C₂₁))
      → PartialFunctor.base (partial-functor-sigma H₂₁) x₁ ≡ just x₁'
      → PartialFunctor.base (partial-functor-sigma H₂₂)
        (Functor.base (functor-sigma F₂) x₁)
      ≡ just (Functor.base (functor-sigma G₂) x₁')
    base (x₁₁ , x₂₁) _
      with Dependent₁PartialFunctor.base H₂₁ x₁₁ x₂₁
      | inspect (Dependent₁PartialFunctor.base H₂₁ x₁₁) x₂₁
    base (x₁₁ , x₂₁) refl | just _ | [ p ]
      with Dependent₁PartialFunctor.base H₂₂ (Functor.base F₁ x₁₁)
        (Dependent₁Functor.base F₂ x₁₁ x₂₁)
      | Dependent₁PartialFunctorSquare.base s x₁₁ x₂₁ p
    ... | _ | refl
      = refl

    map'
      : {x₁ y₁ : Category.Object (category-sigma C₂₁)}
      → {x₂ y₂ : Category.Object (category-sigma C₂₂)}
      → {x₁' y₁' : Category.Object (category-sigma D₂₁)}
      → {x₂' y₂' : Category.Object (category-sigma D₂₂)}
      → (p₁ : PartialFunctor.base (partial-functor-sigma H₂₁) x₁ ≡ just x₁')
      → (p₂ : PartialFunctor.base (partial-functor-sigma H₂₂) x₂ ≡ just x₂')
      → (q₁ : PartialFunctor.base (partial-functor-sigma H₂₁) y₁ ≡ just y₁')
      → (q₂ : PartialFunctor.base (partial-functor-sigma H₂₂) y₂ ≡ just y₂')
      → (f₁ : Category.Arrow (category-sigma C₂₁) x₁ y₁)
      → {f₂ : Category.Arrow (category-sigma C₂₂) x₂ y₂}
      → Category.ArrowEqual'
        (category-sigma C₂₂)
        (Functor.map (functor-sigma F₂) f₁) f₂
      → Category.ArrowEqual'
        (category-sigma D₂₂)
        (PartialFunctor.map (partial-functor-sigma H₂₂) p₂ q₂ f₂)
        (Functor.map (functor-sigma G₂)
          (PartialFunctor.map (partial-functor-sigma H₂₁) p₁ q₁ f₁))
    map'
      {x₁ = (x₁₁ , x₂₁)} {y₁ = (y₁₁ , y₂₁)}
      {x₂ = (x₁₂ , x₂₂)} {y₂ = (y₁₂ , y₂₂)}
      _ _ _ _ _ _
      with Dependent₁PartialFunctor.base H₂₁ x₁₁ x₂₁
      | inspect (Dependent₁PartialFunctor.base H₂₁ x₁₁) x₂₁
      | Dependent₁PartialFunctor.base H₂₂ x₁₂ x₂₂
      | inspect (Dependent₁PartialFunctor.base H₂₂ x₁₂) x₂₂
      | Dependent₁PartialFunctor.base H₂₁ y₁₁ y₂₁
      | inspect (Dependent₁PartialFunctor.base H₂₁ y₁₁) y₂₁
      | Dependent₁PartialFunctor.base H₂₂ y₁₂ y₂₂
      | inspect (Dependent₁PartialFunctor.base H₂₂ y₁₂) y₂₂
    map'
      {x₁ = (x₁₁ , x₂₁)} {y₁ = (y₁₁ , _)} refl refl refl refl
      (CategorySigma.arrow f₁₁ f₂₁ refl)
      {f₂ = CategorySigma.arrow f₁₂ _ refl}
      (any (CategorySigma.arrow-equal r₁ r₂))
      | just _ | [ p₁ ] | just _ | [ p₂ ] | just _ | [ q₁ ] | just _ | [ q₂ ]
      = arrow-equal-sigma D₂₂
        (Maybe.just-injective (trans (sym p₂)
          (Dependent₁PartialFunctorSquare.base s x₁₁ x₂₁ p₁)))
        (any (Category.arrow-sym C₁₂ r₁))
        (Dependent₁PartialFunctorSquare.map'' s y₁₁
          (Dependent₁PartialFunctor.base-square H₂₁ f₁₁ x₂₁ p₁) q₁
          (Dependent₁PartialFunctor.base-square H₂₂ f₁₂
            (Dependent₁Functor.base F₂ x₁₁ x₂₁) p₂) q₂ f₂₁ r₂)

    map
      : {x₁ y₁ : Category.Object (category-sigma C₂₁)}
      → {x₁' y₁' : Category.Object (category-sigma D₂₁)}
      → (p₁ : PartialFunctor.base (partial-functor-sigma H₂₁) x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-sigma H₂₁) y₁ ≡ just y₁')
      → (f₁ : Category.Arrow (category-sigma C₂₁) x₁ y₁)
      → Category.ArrowEqual
        (category-sigma D₂₂)
        (PartialFunctor.map
          (partial-functor-sigma H₂₂)
          (base x₁ p₁)
          (base y₁ q₁)
          (Functor.map (functor-sigma F₂) f₁))
        (Functor.map
          (functor-sigma G₂)
          (PartialFunctor.map (partial-functor-sigma H₂₁) p₁ q₁ f₁))
    map {x₁ = x₁} {y₁ = y₁} p₁ q₁ f₁
      = any'
      $ map' p₁ (base x₁ p₁) q₁ (base y₁ q₁) f₁
      $ Category.arrow-refl' (category-sigma C₂₂)

  partial-functor-square-sigma
    : Dependent₁PartialFunctorSquare F₂ G₂ H₂₁ H₂₂
    → PartialFunctorSquare
      (functor-sigma F₂)
      (functor-sigma G₂)
      (partial-functor-sigma H₂₁)
      (partial-functor-sigma H₂₂)
  partial-functor-square-sigma s
    = record {PartialFunctorSquareSigma s}

