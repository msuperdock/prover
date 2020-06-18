module Prover.Category.Partial.Sigma where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; Functor)
open import Prover.Category.Partial
  using (PartialDependentFunctor; PartialDependentFunctorSquare; PartialFunctor;
    PartialFunctorSquare)
open import Prover.Category.Sigma
  using (module CategorySigma; category-sigma; functor-sigma)
open import Prover.Prelude

-- ## PartialFunctor

module _
  {C₁ : Category}
  {C₂ D₂ : DependentCategory C₁}
  where

  module PartialFunctorSigma
    (F₂ : PartialDependentFunctor C₂ D₂)
    where

    base
      : Category.Object (category-sigma C₂)
      → Maybe (Category.Object (category-sigma D₂))
    base (x₁ , x₂)
      with PartialDependentFunctor.base F₂ x₁ x₂
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
      with PartialDependentFunctor.base F₂ x₁ x₂
      | inspect (PartialDependentFunctor.base F₂ x₁) x₂
      | PartialDependentFunctor.base F₂ y₁ y₂
      | inspect (PartialDependentFunctor.base F₂ y₁) y₂
    map {x = (_ , x₂)} {y = (y₁ , _)} refl refl
      (CategorySigma.arrow y₂'' f₁ f₂ p₂)
      | just x₂' | [ q₂ ] | just y₂' | [ r₂ ]
      = record
      { domain
        = DependentCategory.base D₂ f₁ x₂'
      ; arrow₁
        = f₁
      ; arrow₂
        = PartialDependentFunctor.map F₂ y₁
          (trans (sub (PartialDependentFunctor.base F₂ y₁) (sym p₂))
            (PartialDependentFunctor.base-commutative F₂ f₁ x₂ q₂)) r₂ f₂
      ; valid
        = refl
      }

    abstract

      map-identity₂
        : (x₁ : Category.Object C₁)
        → {x₂' x₂'' : DependentCategory.Object D₂ x₁}
        → (x₂ : DependentCategory.Object C₂ x₁)
        → (p₂ : PartialDependentFunctor.base F₂ x₁ x₂ ≡ just x₂'')
        → (q₂ : PartialDependentFunctor.base F₂ x₁ x₂ ≡ just x₂')
        → x₂'' ≡ x₂'
        → PartialDependentFunctor.map F₂ x₁ p₂ q₂
          (DependentCategory.identity C₂ x₁ x₂)
        ≅ DependentCategory.identity D₂ x₁ x₂'
      map-identity₂ x₁ x₂ p₂ q₂ refl
        with irrelevant p₂ q₂
      ... | refl
        = PartialDependentFunctor.map-identity F₂ x₁ x₂ p₂
  
      map-identity
        : {x' : Category.Object (category-sigma D₂)}
        → (x : Category.Object (category-sigma C₂))
        → (p : base x ≡ just x')
        → map p p (Category.identity (category-sigma C₂) x)
          ≡ Category.identity (category-sigma D₂) x'
      map-identity (x₁ , x₂) _
        with PartialDependentFunctor.base F₂ x₁ x₂
        | inspect (PartialDependentFunctor.base F₂ x₁) x₂
      map-identity (x₁ , x₂) refl
        | just x₂' | [ p₂ ]
        = CategorySigma.arrow-eq D₂
          (DependentCategory.base-identity D₂ x₁ x₂') refl
          (map-identity₂ x₁ x₂
            (trans
              (sub (PartialDependentFunctor.base F₂ x₁)
                (sym (DependentCategory.base-identity C₂ x₁ x₂)))
              (PartialDependentFunctor.base-commutative F₂
                (Category.identity C₁ x₁) x₂ p₂)) p₂
            (DependentCategory.base-identity D₂ x₁ x₂'))
  
      map-compose₂
        : (x₁ : Category.Object C₁)
        → {w₂ x₂ y₂ z₂ : DependentCategory.Object C₂ x₁}
        → {w₂' w₂'' x₂' z₂' : DependentCategory.Object D₂ x₁}
        → {g₂' : DependentCategory.Arrow D₂ x₁ w₂' x₂'}
        → (p₂ : PartialDependentFunctor.base F₂ x₁ w₂ ≡ just w₂'')
        → (q₂ : PartialDependentFunctor.base F₂ x₁ x₂ ≡ just x₂')
        → (r₂ : PartialDependentFunctor.base F₂ x₁ y₂ ≡ just x₂')
        → (s₂ : PartialDependentFunctor.base F₂ x₁ z₂ ≡ just z₂')
        → (t₂ : x₂ ≡ y₂)
        → (f₂ : DependentCategory.Arrow C₂ x₁ y₂ z₂)
        → (g₂ : DependentCategory.Arrow C₂ x₁ w₂ x₂)
        → w₂'' ≡ w₂'
        → PartialDependentFunctor.map F₂ x₁ p₂ q₂ g₂ ≅ g₂'
        → PartialDependentFunctor.map F₂ x₁ p₂ s₂
          (DependentCategory.compose-eq C₂ x₁ t₂ f₂ g₂)
        ≅ DependentCategory.compose D₂ x₁
          (PartialDependentFunctor.map F₂ x₁ r₂ s₂ f₂) g₂'
      map-compose₂ x₁ p₂ q₂ r₂ s₂ refl f₂ g₂ refl refl
        with irrelevant q₂ r₂
      ... | refl
        = PartialDependentFunctor.map-compose F₂ x₁ p₂ q₂ s₂ f₂ g₂
  
      map-compose₂'
        : {x₁ y₁ : Category.Object C₁}
        → {x₂ y₂ : DependentCategory.Object C₂ x₁}
        → {x₂' y₂' : DependentCategory.Object D₂ x₁}
        → {y₂'' : DependentCategory.Object D₂ y₁}
        → (f₁ : Category.Arrow C₁ x₁ y₁)
        → (p₂ : PartialDependentFunctor.base F₂ x₁ x₂ ≡ just x₂')
        → (q₂ : PartialDependentFunctor.base F₂ x₁ y₂ ≡ just y₂')
        → (r₂ : PartialDependentFunctor.base F₂ y₁
          (DependentCategory.base C₂ f₁ x₂)
          ≡ just y₂'')
        → (f₂ : DependentCategory.Arrow C₂ x₁ x₂ y₂)
        → DependentCategory.base D₂ f₁ x₂' ≡ y₂''
        → PartialDependentFunctor.map F₂ y₁ r₂
          (PartialDependentFunctor.base-commutative F₂ f₁ y₂ q₂)
          (DependentCategory.map C₂ f₁ f₂)
        ≅ DependentCategory.map D₂ f₁
          (PartialDependentFunctor.map F₂ x₁ p₂ q₂ f₂)
      map-compose₂' {x₂ = x₂} f₁ p₂ q₂ r₂ f₂ refl
        with irrelevant r₂
          (PartialDependentFunctor.base-commutative F₂ f₁ x₂ p₂)
      ... | refl
        = PartialDependentFunctor.map-commutative F₂ f₁ p₂ q₂ f₂
  
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
        with PartialDependentFunctor.base F₂ x₁ x₂
        | inspect (PartialDependentFunctor.base F₂ x₁) x₂
        | PartialDependentFunctor.base F₂ y₁ y₂
        | inspect (PartialDependentFunctor.base F₂ y₁) y₂
        | PartialDependentFunctor.base F₂ z₁ z₂
        | inspect (PartialDependentFunctor.base F₂ z₁) z₂
      map-compose {x = (_ , x₂)} {y = (y₁ , y₂)} {z = (z₁ , _)} refl refl refl
        (CategorySigma.arrow _ f₁ f₂ p₂)
        (CategorySigma.arrow _ g₁ g₂ q₂)
        | just x₂' | [ p₂' ] | just _ | [ q₂' ] | just _ | [ r₂' ]
        = CategorySigma.arrow-eq D₂
          (DependentCategory.base-compose D₂ f₁ g₁ x₂') refl
        $ map-compose₂ z₁ p₂''
          (PartialDependentFunctor.base-commutative F₂ f₁ y₂ q₂')
          (trans (sub (PartialDependentFunctor.base F₂ z₁) (sym p₂))
            (PartialDependentFunctor.base-commutative F₂ f₁ y₂ q₂')) r₂' p₂ f₂
          (DependentCategory.map C₂ f₁ g₂)
          (DependentCategory.base-compose D₂ f₁ g₁ x₂')
        $ map-compose₂' f₁
          (trans (sub (PartialDependentFunctor.base F₂ y₁) (sym q₂))
            (PartialDependentFunctor.base-commutative F₂ g₁ x₂ p₂')) q₂' p₂'' g₂
          (sym (DependentCategory.base-compose D₂ f₁ g₁ x₂'))
        where
          p₂'' = trans
            (sub (PartialDependentFunctor.base F₂ z₁)
              (sym (trans (DependentCategory.base-compose C₂ f₁ g₁ x₂)
                (sub (DependentCategory.base C₂ f₁) q₂))))
            (PartialDependentFunctor.base-commutative F₂
              (Category.compose C₁ f₁ g₁) x₂ p₂')

  partial-functor-sigma
    : (F₂ : PartialDependentFunctor C₂ D₂)
    → PartialFunctor
      (category-sigma C₂)
      (category-sigma D₂)
  partial-functor-sigma F₂
    = record {PartialFunctorSigma F₂}

-- ## PartialFunctorSquare

module _
  {C₁₁ C₂₁ : Category}
  {C₁₂ D₁₂ : DependentCategory C₁₁}
  {C₂₂ D₂₂ : DependentCategory C₂₁}
  {F₂ : DependentFunctor C₁₂ C₂₂}
  {G₂ : DependentFunctor D₁₂ D₂₂}
  {H₁₂ : PartialDependentFunctor C₁₂ D₁₂}
  {H₂₂ : PartialDependentFunctor C₂₂ D₂₂}
  where

  module PartialFunctorSquareSigma
    (s : PartialDependentFunctorSquare F₂ G₂ H₁₂ H₂₂)
    where

    base
      : {x₁' : Category.Object (category-sigma D₁₂)}
      → (x₁ : Category.Object (category-sigma C₁₂))
      → PartialFunctor.base (partial-functor-sigma H₁₂) x₁ ≡ just x₁'
      → PartialFunctor.base (partial-functor-sigma H₂₂)
        (Functor.base (functor-sigma F₂) x₁)
      ≡ just (Functor.base (functor-sigma G₂) x₁')
    base (x₁₁ , x₁₂) _
      with PartialDependentFunctor.base H₁₂ x₁₁ x₁₂
      | inspect (PartialDependentFunctor.base H₁₂ x₁₁) x₁₂
    base (x₁₁ , x₁₂) refl | just _ | [ p ]
      with DependentFunctor.base F₂ x₁₁
      | PartialDependentFunctorSquare.base s x₁₁
      | DependentFunctor.base' F₂ x₁₁ x₁₂
      | PartialDependentFunctor.base H₂₂
        (DependentFunctor.base F₂ x₁₁)
        (DependentFunctor.base' F₂ x₁₁ x₁₂)
      | PartialDependentFunctorSquare.base' s x₁₁ x₁₂ p
    ... | _ | refl | _ | _ | refl
      = refl

    map-eq
      : {x₁ y₁ : Category.Object (category-sigma C₁₂)}
      → {x₁' y₁' : Category.Object (category-sigma D₁₂)}
      → {x₂ y₂ : Category.Object (category-sigma C₂₂)}
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
      with PartialDependentFunctor.base H₁₂ x₁₁ x₁₂
      | inspect (PartialDependentFunctor.base H₁₂ x₁₁) x₁₂
      | PartialDependentFunctor.base H₁₂ y₁₁ y₁₂
      | inspect (PartialDependentFunctor.base H₁₂ y₁₁) y₁₂
      | PartialDependentFunctor.base H₂₂ x₂₁ x₂₂
      | inspect (PartialDependentFunctor.base H₂₂ x₂₁) x₂₂
      | PartialDependentFunctor.base H₂₂ y₂₁ y₂₂
      | inspect (PartialDependentFunctor.base H₂₂ y₂₁) y₂₂
    map-eq {x₁ = (x₁₁ , x₁₂)} {y₁ = (y₁₁ , y₁₂)}
      refl refl refl refl (CategorySigma.arrow _ f₁₁ f₁₂ r₂) refl refl refl
      | just x₁₂' | [ p₁ ] | just _ | [ q₁ ]
      | just _ | [ p₂ ] | just _ | [ q₂ ]
      = CategorySigma.arrow-eq' D₂₂
        (Sigma.comma-eq p₁' p₂')
        (Sigma.comma-eq q₁' q₂') p₂'' r₁'
        (PartialDependentFunctorSquare.map-eq' s y₁₁
          (trans
            (sub (PartialDependentFunctor.base H₁₂ y₁₁) (sym r₂))
            (PartialDependentFunctor.base-commutative H₁₂ f₁₁ x₁₂ p₁)) q₁
          (trans
            (sub
              (PartialDependentFunctor.base H₂₂
                (DependentFunctor.base F₂ y₁₁))
              (sym (trans (sym (DependentFunctor.base-commutative F₂ f₁₁ x₁₂))
                (sub (DependentFunctor.base' F₂ y₁₁) r₂))))
            (PartialDependentFunctor.base-commutative H₂₂
              (DependentFunctor.map F₂ f₁₁)
              (DependentFunctor.base' F₂ x₁₁ x₁₂) p₂)) q₂ f₁₂
          (sym p₂'')
          (sym q₂'))
      where
        p₁' = PartialDependentFunctorSquare.base s x₁₁
        q₁' = PartialDependentFunctorSquare.base s y₁₁
        r₁' = PartialDependentFunctorSquare.map s f₁₁
        p₂' = Maybe.just-injective' (DependentCategory.Object D₂₂) p₁'
          (trans (sym p₂) (PartialDependentFunctorSquare.base' s x₁₁ x₁₂ p₁))
        q₂' = Maybe.just-injective' (DependentCategory.Object D₂₂) q₁'
          (trans (sym q₂) (PartialDependentFunctorSquare.base' s y₁₁ y₁₂ q₁))
        p₂'' = trans (DependentCategory.base-eq D₂₂ p₁' q₁' p₂' r₁')
          (sym (DependentFunctor.base-commutative G₂ f₁₁ x₁₂'))

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
    : PartialDependentFunctorSquare F₂ G₂ H₁₂ H₂₂
    → PartialFunctorSquare
      (functor-sigma F₂)
      (functor-sigma G₂)
      (partial-functor-sigma H₁₂)
      (partial-functor-sigma H₂₂)
  partial-functor-square-sigma s
    = record {PartialFunctorSquareSigma s}

