module Prover.Category.Partial.Sigma where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Dependent1.Partial
  using (Dependent₁PartialFunctor; Dependent₁PartialFunctorSquare)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Sigma
  using (module CategorySigma; category-sigma; functor-sigma)
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
      (CategorySigma.arrow _ f₁ f₂ p₂)
      | just x₂' | [ q₂ ] | just _ | [ r₂ ]
      = record
      { domain
        = Dependent₁Category.base D₂ f₁ x₂'
      ; arrow₁
        = f₁
      ; arrow₂
        = Dependent₁PartialFunctor.map F₂ y₁
          (trans (sub (Dependent₁PartialFunctor.base F₂ y₁) (sym p₂))
            (Dependent₁PartialFunctor.base-commutative F₂ f₁ x₂ q₂)) r₂ f₂
      ; valid
        = refl
      }

    abstract

      map-identity₂
        : (x₁ : Category.Object C₁)
        → {x₂' x₂'' : Dependent₁Category.Object D₂ x₁}
        → (x₂ : Dependent₁Category.Object C₂ x₁)
        → (p₂ : Dependent₁PartialFunctor.base F₂ x₁ x₂ ≡ just x₂'')
        → (q₂ : Dependent₁PartialFunctor.base F₂ x₁ x₂ ≡ just x₂')
        → x₂'' ≡ x₂'
        → Dependent₁PartialFunctor.map F₂ x₁ p₂ q₂
          (Dependent₁Category.identity C₂ x₁ x₂)
        ≅ Dependent₁Category.identity D₂ x₁ x₂'
      map-identity₂ x₁ x₂ p₂ q₂ refl
        with irrelevant p₂ q₂
      ... | refl
        = Dependent₁PartialFunctor.map-identity F₂ x₁ x₂ p₂
  
      map-identity
        : {x' : Category.Object (category-sigma D₂)}
        → (x : Category.Object (category-sigma C₂))
        → (p : base x ≡ just x')
        → map p p (Category.identity (category-sigma C₂) x)
          ≡ Category.identity (category-sigma D₂) x'
      map-identity (x₁ , x₂) _
        with Dependent₁PartialFunctor.base F₂ x₁ x₂
        | inspect (Dependent₁PartialFunctor.base F₂ x₁) x₂
      map-identity (x₁ , x₂) refl
        | just x₂' | [ p₂ ]
        = CategorySigma.arrow-eq D₂
          (Dependent₁Category.base-identity D₂ x₁ x₂') refl
          (map-identity₂ x₁ x₂
            (trans
              (sub (Dependent₁PartialFunctor.base F₂ x₁)
                (sym (Dependent₁Category.base-identity C₂ x₁ x₂)))
              (Dependent₁PartialFunctor.base-commutative F₂
                (Category.identity C₁ x₁) x₂ p₂)) p₂
            (Dependent₁Category.base-identity D₂ x₁ x₂'))
  
      map-compose₂
        : (x₁ : Category.Object C₁)
        → {w₂ x₂ y₂ z₂ : Dependent₁Category.Object C₂ x₁}
        → {w₂' w₂'' x₂' z₂' : Dependent₁Category.Object D₂ x₁}
        → {g₂' : Dependent₁Category.Arrow D₂ x₁ w₂' x₂'}
        → (p₂ : Dependent₁PartialFunctor.base F₂ x₁ w₂ ≡ just w₂'')
        → (q₂ : Dependent₁PartialFunctor.base F₂ x₁ x₂ ≡ just x₂')
        → (r₂ : Dependent₁PartialFunctor.base F₂ x₁ y₂ ≡ just x₂')
        → (s₂ : Dependent₁PartialFunctor.base F₂ x₁ z₂ ≡ just z₂')
        → (t₂ : x₂ ≡ y₂)
        → (f₂ : Dependent₁Category.Arrow C₂ x₁ y₂ z₂)
        → (g₂ : Dependent₁Category.Arrow C₂ x₁ w₂ x₂)
        → w₂'' ≡ w₂'
        → Dependent₁PartialFunctor.map F₂ x₁ p₂ q₂ g₂ ≅ g₂'
        → Dependent₁PartialFunctor.map F₂ x₁ p₂ s₂
          (Dependent₁Category.compose-eq C₂ x₁ t₂ f₂ g₂)
        ≅ Dependent₁Category.compose D₂ x₁
          (Dependent₁PartialFunctor.map F₂ x₁ r₂ s₂ f₂) g₂'
      map-compose₂ x₁ p₂ q₂ r₂ s₂ refl f₂ g₂ refl refl
        with irrelevant q₂ r₂
      ... | refl
        = Dependent₁PartialFunctor.map-compose F₂ x₁ p₂ q₂ s₂ f₂ g₂
  
      map-compose₂'
        : {x₁ y₁ : Category.Object C₁}
        → {x₂ y₂ : Dependent₁Category.Object C₂ x₁}
        → {x₂' y₂' : Dependent₁Category.Object D₂ x₁}
        → {y₂'' : Dependent₁Category.Object D₂ y₁}
        → (f₁ : Category.Arrow C₁ x₁ y₁)
        → (p₂ : Dependent₁PartialFunctor.base F₂ x₁ x₂ ≡ just x₂')
        → (q₂ : Dependent₁PartialFunctor.base F₂ x₁ y₂ ≡ just y₂')
        → (r₂ : Dependent₁PartialFunctor.base F₂ y₁
          (Dependent₁Category.base C₂ f₁ x₂)
          ≡ just y₂'')
        → (f₂ : Dependent₁Category.Arrow C₂ x₁ x₂ y₂)
        → Dependent₁Category.base D₂ f₁ x₂' ≡ y₂''
        → Dependent₁PartialFunctor.map F₂ y₁ r₂
          (Dependent₁PartialFunctor.base-commutative F₂ f₁ y₂ q₂)
          (Dependent₁Category.map C₂ f₁ f₂)
        ≅ Dependent₁Category.map D₂ f₁
          (Dependent₁PartialFunctor.map F₂ x₁ p₂ q₂ f₂)
      map-compose₂' {x₂ = x₂} f₁ p₂ q₂ r₂ f₂ refl
        with irrelevant r₂
          (Dependent₁PartialFunctor.base-commutative F₂ f₁ x₂ p₂)
      ... | refl
        = Dependent₁PartialFunctor.map-commutative F₂ f₁ p₂ q₂ f₂
  
      map-compose
        : {x y z : Category.Object (category-sigma C₂)}
        → {x' y' z' : Category.Object (category-sigma D₂)}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow (category-sigma C₂) y z)
        → (g : Category.Arrow (category-sigma C₂) x y)
        → map p r (Category.compose (category-sigma C₂) f g)
          ≡ Category.compose (category-sigma D₂) (map q r f) (map p q g)
      map-compose {x = (x₁ , x₂)} {y = (y₁ , y₂)} {z = (z₁ , z₂)} _ _ _ _ _
        with Dependent₁PartialFunctor.base F₂ x₁ x₂
        | inspect (Dependent₁PartialFunctor.base F₂ x₁) x₂
        | Dependent₁PartialFunctor.base F₂ y₁ y₂
        | inspect (Dependent₁PartialFunctor.base F₂ y₁) y₂
        | Dependent₁PartialFunctor.base F₂ z₁ z₂
        | inspect (Dependent₁PartialFunctor.base F₂ z₁) z₂
      map-compose {x = (_ , x₂)} {y = (y₁ , y₂)} {z = (z₁ , _)} refl refl refl
        (CategorySigma.arrow _ f₁ f₂ p₂)
        (CategorySigma.arrow _ g₁ g₂ q₂)
        | just x₂' | [ p₂' ] | just _ | [ q₂' ] | just _ | [ r₂' ]
        = CategorySigma.arrow-eq D₂
          (Dependent₁Category.base-compose D₂ f₁ g₁ x₂') refl
        $ map-compose₂ z₁ s₂
          (Dependent₁PartialFunctor.base-commutative F₂ f₁ y₂ q₂')
          (trans (sub (Dependent₁PartialFunctor.base F₂ z₁) (sym p₂))
            (Dependent₁PartialFunctor.base-commutative F₂ f₁ y₂ q₂')) r₂' p₂ f₂
          (Dependent₁Category.map C₂ f₁ g₂)
          (Dependent₁Category.base-compose D₂ f₁ g₁ x₂')
        $ map-compose₂' f₁
          (trans (sub (Dependent₁PartialFunctor.base F₂ y₁) (sym q₂))
            (Dependent₁PartialFunctor.base-commutative F₂ g₁ x₂ p₂')) q₂' s₂ g₂
          (sym (Dependent₁Category.base-compose D₂ f₁ g₁ x₂'))
        where
          s₂ = trans
            (sub (Dependent₁PartialFunctor.base F₂ z₁)
              (sym (trans (Dependent₁Category.base-compose C₂ f₁ g₁ x₂)
                (sub (Dependent₁Category.base C₂ f₁) q₂))))
            (Dependent₁PartialFunctor.base-commutative F₂
              (Category.compose C₁ f₁ g₁) x₂ p₂')

  partial-functor-sigma
    : Dependent₁PartialFunctor C₂ D₂
    → PartialFunctor
      (category-sigma C₂)
      (category-sigma D₂)
  partial-functor-sigma F₂
    = record {PartialFunctorSigma F₂}

-- ## PartialFunctorSquare

module _
  {C₁₁ C₂₁ : Category}
  {C₁₂ D₁₂ : Dependent₁Category C₁₁}
  {C₂₂ D₂₂ : Dependent₁Category C₂₁}
  {F₂ : Dependent₁Functor C₁₂ C₂₂}
  {G₂ : Dependent₁Functor D₁₂ D₂₂}
  {H₁₂ : Dependent₁PartialFunctor C₁₂ D₁₂}
  {H₂₂ : Dependent₁PartialFunctor C₂₂ D₂₂}
  where

  module PartialFunctorSquareSigma
    (s : Dependent₁PartialFunctorSquare F₂ G₂ H₁₂ H₂₂)
    where

    base
      : {x₁' : Category.Object (category-sigma D₁₂)}
      → (x₁ : Category.Object (category-sigma C₁₂))
      → PartialFunctor.base (partial-functor-sigma H₁₂) x₁ ≡ just x₁'
      → PartialFunctor.base (partial-functor-sigma H₂₂)
        (Functor.base (functor-sigma F₂) x₁)
      ≡ just (Functor.base (functor-sigma G₂) x₁')
    base (x₁₁ , x₁₂) _
      with Dependent₁PartialFunctor.base H₁₂ x₁₁ x₁₂
      | inspect (Dependent₁PartialFunctor.base H₁₂ x₁₁) x₁₂
    base (x₁₁ , x₁₂) refl | just _ | [ p ]
      with Dependent₁Functor.base F₂ x₁₁
      | Dependent₁PartialFunctorSquare.base s x₁₁
      | Dependent₁Functor.base' F₂ x₁₁ x₁₂
      | Dependent₁PartialFunctor.base H₂₂
        (Dependent₁Functor.base F₂ x₁₁)
        (Dependent₁Functor.base' F₂ x₁₁ x₁₂)
      | Dependent₁PartialFunctorSquare.base' s x₁₁ x₁₂ p
    ... | _ | refl | _ | _ | refl
      = refl

    map-eq
      : {x₁ y₁ : Category.Object (category-sigma C₁₂)}
      → {x₂ y₂ : Category.Object (category-sigma C₂₂)}
      → {x₁' y₁' : Category.Object (category-sigma D₁₂)}
      → {x₂' y₂' : Category.Object (category-sigma D₂₂)}
      → {f₂ : Category.Arrow (category-sigma C₂₂) x₂ y₂}
      → (p₁ : PartialFunctor.base (partial-functor-sigma H₁₂) x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-sigma H₁₂) y₁ ≡ just y₁')
      → (p₂ : PartialFunctor.base (partial-functor-sigma H₂₂) x₂ ≡ just x₂')
      → (q₂ : PartialFunctor.base (partial-functor-sigma H₂₂) y₂ ≡ just y₂')
      → (f₁ : Category.Arrow (category-sigma C₁₂) x₁ y₁)
      → Functor.base (functor-sigma F₂) x₁ ≡ x₂
      → Functor.base (functor-sigma F₂) y₁ ≡ y₂
      → Functor.map (functor-sigma F₂) f₁ ≅ f₂
      → PartialFunctor.map (partial-functor-sigma H₂₂) p₂ q₂ f₂
      ≅ Functor.map (functor-sigma G₂)
        (PartialFunctor.map (partial-functor-sigma H₁₂) p₁ q₁ f₁)
    map-eq
      {x₁ = (x₁₁ , x₁₂)} {y₁ = (y₁₁ , y₁₂)}
      {x₂ = (x₂₁ , x₂₂)} {y₂ = (y₂₁ , y₂₂)}
      _ _ _ _ _ _ _ _
      with Dependent₁PartialFunctor.base H₁₂ x₁₁ x₁₂
      | inspect (Dependent₁PartialFunctor.base H₁₂ x₁₁) x₁₂
      | Dependent₁PartialFunctor.base H₁₂ y₁₁ y₁₂
      | inspect (Dependent₁PartialFunctor.base H₁₂ y₁₁) y₁₂
      | Dependent₁PartialFunctor.base H₂₂ x₂₁ x₂₂
      | inspect (Dependent₁PartialFunctor.base H₂₂ x₂₁) x₂₂
      | Dependent₁PartialFunctor.base H₂₂ y₂₁ y₂₂
      | inspect (Dependent₁PartialFunctor.base H₂₂ y₂₁) y₂₂
    map-eq {x₁ = (x₁₁ , x₁₂)} {y₁ = (y₁₁ , y₁₂)}
      refl refl refl refl (CategorySigma.arrow _ f₁₁ f₁₂ r₂) refl refl refl
      | just x₁₂' | [ p₁ ] | just _ | [ q₁ ]
      | just _ | [ p₂ ] | just _ | [ q₂ ]
      = CategorySigma.arrow-eq' D₂₂
        (Sigma.comma-eq p₁' p₂')
        (Sigma.comma-eq q₁' q₂') p₂'' r₁'
        (Dependent₁PartialFunctorSquare.map-eq' s y₁₁
          (trans
            (sub (Dependent₁PartialFunctor.base H₁₂ y₁₁) (sym r₂))
            (Dependent₁PartialFunctor.base-commutative H₁₂ f₁₁ x₁₂ p₁)) q₁
          (trans
            (sub
              (Dependent₁PartialFunctor.base H₂₂
                (Dependent₁Functor.base F₂ y₁₁))
              (sym (trans (sym (Dependent₁Functor.base-commutative F₂ f₁₁ x₁₂))
                (sub (Dependent₁Functor.base' F₂ y₁₁) r₂))))
            (Dependent₁PartialFunctor.base-commutative H₂₂
              (Dependent₁Functor.map F₂ f₁₁)
              (Dependent₁Functor.base' F₂ x₁₁ x₁₂) p₂)) q₂ f₁₂
          (sym p₂'')
          (sym q₂'))
      where
        p₁' = Dependent₁PartialFunctorSquare.base s x₁₁
        q₁' = Dependent₁PartialFunctorSquare.base s y₁₁
        r₁' = Dependent₁PartialFunctorSquare.map s f₁₁
        p₂' = Maybe.just-injective' (Dependent₁Category.Object D₂₂) p₁'
          (trans (sym p₂) (Dependent₁PartialFunctorSquare.base' s x₁₁ x₁₂ p₁))
        q₂' = Maybe.just-injective' (Dependent₁Category.Object D₂₂) q₁'
          (trans (sym q₂) (Dependent₁PartialFunctorSquare.base' s y₁₁ y₁₂ q₁))
        p₂'' = trans (Dependent₁Category.base-eq D₂₂ p₁' q₁' p₂' r₁')
          (sym (Dependent₁Functor.base-commutative G₂ f₁₁ x₁₂'))

    map
      : {x₁ y₁ : Category.Object (category-sigma C₁₂)}
      → {x₁' y₁' : Category.Object (category-sigma D₁₂)}
      → (p₁ : PartialFunctor.base (partial-functor-sigma H₁₂) x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-sigma H₁₂) y₁ ≡ just y₁')
      → (f₁ : Category.Arrow (category-sigma C₁₂) x₁ y₁)
      → PartialFunctor.map (partial-functor-sigma H₂₂) (base x₁ p₁) (base y₁ q₁)
        (Functor.map (functor-sigma F₂) f₁)
      ≡ Functor.map (functor-sigma G₂)
        (PartialFunctor.map (partial-functor-sigma H₁₂) p₁ q₁ f₁)
    map {x₁ = x₁} {y₁ = y₁} p₁ q₁ f₁
      = map-eq p₁ q₁ (base x₁ p₁) (base y₁ q₁) f₁ refl refl refl

  partial-functor-square-sigma
    : Dependent₁PartialFunctorSquare F₂ G₂ H₁₂ H₂₂
    → PartialFunctorSquare
      (functor-sigma F₂)
      (functor-sigma G₂)
      (partial-functor-sigma H₁₂)
      (partial-functor-sigma H₂₂)
  partial-functor-square-sigma s
    = record {PartialFunctorSquareSigma s}

