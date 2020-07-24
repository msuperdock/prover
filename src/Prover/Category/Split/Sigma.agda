module Prover.Category.Split.Sigma where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; Functor; FunctorSquare)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Partial.Sigma
  using (partial-functor-sigma; partial-functor-square-sigma)
open import Prover.Category.Sigma
  using (module CategorySigma; category-sigma; functor-sigma;
    functor-square-sigma)
open import Prover.Category.Split
  using (SplitDependentFunctor; SplitDependentFunctorSquare; SplitFunctor;
    SplitFunctorSquare)
open import Prover.Prelude

-- ## SplitFunctor

module _
  {C₁ : Category}
  {C₂ D₂ : DependentCategory C₁}
  where

  module SplitFunctorSigma
    (F₂ : SplitDependentFunctor C₂ D₂)
    where

    partial-functor
      : PartialFunctor
        (category-sigma C₂)
        (category-sigma D₂)
    partial-functor
      = partial-functor-sigma
        (SplitDependentFunctor.partial-dependent-functor F₂)

    open PartialFunctor partial-functor

    functor
      : Functor
        (category-sigma D₂)
        (category-sigma C₂)
    functor
      = functor-sigma
        (SplitDependentFunctor.dependent-functor F₂)

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase
        : (x' : Category.Object (category-sigma D₂))
        → base (unbase x') ≡ just x'
      base-unbase (x₁ , x₂)
        with SplitDependentFunctor.base F₂ x₁
          (SplitDependentFunctor.unbase F₂ x₁ x₂)
        | SplitDependentFunctor.base-unbase F₂ x₁ x₂
      ... | _ | refl
        = refl
  
      map-unmap₂
        : (x₁ : Category.Object C₁)
        → {x₂' x₂'' y₂' : DependentCategory.Object D₂ x₁}
        → (p₂ : SplitDependentFunctor.base F₂ x₁
          (SplitDependentFunctor.unbase F₂ x₁ x₂')
          ≡ just x₂'')
        → (q₂ : SplitDependentFunctor.base F₂ x₁
          (SplitDependentFunctor.unbase F₂ x₁ y₂')
          ≡ just y₂')
        → (f₂ : DependentCategory.Arrow D₂ x₁ x₂' y₂')
        → x₂'' ≡ x₂'
        → SplitDependentFunctor.map F₂ x₁ p₂ q₂
          (SplitDependentFunctor.unmap F₂ x₁ f₂)
          ≅ f₂
      map-unmap₂ x₁ {x₂' = x₂'} {y₂' = y₂'} p₂ q₂ f₂ refl
        with irrelevant p₂ (SplitDependentFunctor.base-unbase F₂ x₁ x₂')
        | irrelevant q₂ (SplitDependentFunctor.base-unbase F₂ x₁ y₂')
      ... | refl | refl
        = SplitDependentFunctor.map-unmap F₂ x₁ f₂
  
      map-unmap
        : {x' y' : Category.Object (category-sigma D₂)}
        → (f : Category.Arrow (category-sigma D₂) x' y')
        → map (base-unbase x') (base-unbase y') (unmap f) ≡ f
      map-unmap {x' = (x₁ , x₂)} {y' = (y₁ , y₂)}
        (CategorySigma.arrow _ f₁ f₂ p₂)
        with SplitDependentFunctor.base F₂ x₁
          (SplitDependentFunctor.unbase F₂ x₁ x₂)
        | inspect (SplitDependentFunctor.base F₂ x₁)
          (SplitDependentFunctor.unbase F₂ x₁ x₂)
        | SplitDependentFunctor.base-unbase F₂ x₁ x₂
        | SplitDependentFunctor.base F₂ y₁
          (SplitDependentFunctor.unbase F₂ y₁ y₂)
        | inspect (SplitDependentFunctor.base F₂ y₁)
          (SplitDependentFunctor.unbase F₂ y₁ y₂)
        | SplitDependentFunctor.base-unbase F₂ y₁ y₂
      ... | _ | [ q₂ ] | refl | _ | [ r₂ ] | refl
        = CategorySigma.arrow-eq D₂ p₂ refl
          (map-unmap₂ y₁ (trans
            (sub (SplitDependentFunctor.base F₂ y₁) (sym (trans
              (sym (SplitDependentFunctor.unbase-commutative F₂ f₁ x₂))
              (sub (SplitDependentFunctor.unbase F₂ y₁) p₂))))
            (SplitDependentFunctor.base-commutative F₂ f₁
              (SplitDependentFunctor.unbase F₂ x₁ x₂) q₂)) r₂ f₂ p₂)

      normalize-arrow
        : {x' : Category.Object (category-sigma D₂)}
        → (x : Category.Object (category-sigma C₂))
        → base x ≡ just x'
        → Category.Arrow (category-sigma C₂) x (unbase x')
      normalize-arrow (x₁ , x₂) _
        with SplitDependentFunctor.base F₂ x₁ x₂
        | inspect (SplitDependentFunctor.base F₂ x₁) x₂
      normalize-arrow (x₁ , x₂) refl | just _ | [ p₂ ]
        = CategorySigma.arrow x₂
          (Category.identity C₁ x₁)
          (SplitDependentFunctor.normalize-arrow F₂ x₁ x₂ p₂)
          (DependentCategory.base-identity C₂ x₁ x₂)

      normalize-valid₂
        : {x₁ : Category.Object C₁}
        → {x₂' x₂'' : DependentCategory.Object D₂ x₁}
        → (x₂ : DependentCategory.Object C₂ x₁)
        → (p₂ : SplitDependentFunctor.base F₂ x₁ x₂ ≡ just x₂')
        → (p₂' : SplitDependentFunctor.base F₂ x₁ x₂ ≡ just x₂'')
        → (q₂ : SplitDependentFunctor.base F₂ x₁
          (SplitDependentFunctor.unbase F₂ x₁ x₂')
          ≡ just x₂')
        → x₂' ≡ x₂''
        → SplitDependentFunctor.map F₂ x₁ p₂' q₂
          (SplitDependentFunctor.normalize-arrow F₂ x₁ x₂ p₂)
        ≅ DependentCategory.identity D₂ x₁ x₂'
      normalize-valid₂ {x₁ = x₁} {x₂' = x₂'} x₂ p₂ p₂' q₂ refl
        with irrelevant p₂ p₂'
        | irrelevant q₂ (SplitDependentFunctor.base-unbase F₂ x₁ x₂')
      ... | refl | refl
        = SplitDependentFunctor.normalize-valid F₂ x₁ x₂ p₂
  
      normalize-valid
        : {x' : Category.Object (category-sigma D₂)}
        → (x : Category.Object (category-sigma C₂))
        → (p : base x ≡ just x')
        → map p (base-unbase x') (normalize-arrow x p)
          ≡ Category.identity (category-sigma D₂) x'
      normalize-valid (x₁ , x₂) _
        with SplitDependentFunctor.base F₂ x₁ x₂
        | inspect (SplitDependentFunctor.base F₂ x₁) x₂
      normalize-valid (x₁ , x₂) refl | just x₂' | [ p₂ ]
        with SplitDependentFunctor.base F₂ x₁
          (SplitDependentFunctor.unbase F₂ x₁ x₂')
        | inspect (SplitDependentFunctor.base F₂ x₁)
          (SplitDependentFunctor.unbase F₂ x₁ x₂')
        | SplitDependentFunctor.base-unbase F₂ x₁ x₂'
      ... | just _ | [ p₂' ] | refl
        = CategorySigma.arrow-eq D₂
          (DependentCategory.base-identity D₂ x₁ x₂') refl
          (normalize-valid₂ x₂ p₂
            (trans
              (sub (SplitDependentFunctor.base F₂ x₁)
                (sym (DependentCategory.base-identity C₂ x₁ x₂)))
              (SplitDependentFunctor.base-commutative F₂
                (Category.identity C₁ x₁) x₂ p₂)) p₂'
            (sym (DependentCategory.base-identity D₂ x₁ x₂')))

  split-functor-sigma
    : SplitDependentFunctor C₂ D₂
    → SplitFunctor
      (category-sigma C₂)
      (category-sigma D₂)
  split-functor-sigma F₂
    = record {SplitFunctorSigma F₂}

-- ## SplitFunctorSquare

module _
  {C₁₁ C₂₁ : Category}
  {C₁₂ D₁₂ : DependentCategory C₁₁}
  {C₂₂ D₂₂ : DependentCategory C₂₁}
  {F₂ : DependentFunctor C₁₂ C₂₂}
  {G₂ : DependentFunctor D₁₂ D₂₂}
  {H₁₂ : SplitDependentFunctor C₁₂ D₁₂}
  {H₂₂ : SplitDependentFunctor C₂₂ D₂₂}
  where

  module SplitFunctorSquareSigma
    (s : SplitDependentFunctorSquare F₂ G₂ H₁₂ H₂₂)
    where

    partial-functor
      : PartialFunctorSquare
        (functor-sigma F₂)
        (functor-sigma G₂)
        (SplitFunctor.partial-functor (split-functor-sigma H₁₂))
        (SplitFunctor.partial-functor (split-functor-sigma H₂₂))
    partial-functor
      = partial-functor-square-sigma
        (SplitDependentFunctorSquare.partial-dependent-functor s)

    functor
      : FunctorSquare
        (functor-sigma G₂)
        (functor-sigma F₂)
        (SplitFunctor.functor (split-functor-sigma H₁₂))
        (SplitFunctor.functor (split-functor-sigma H₂₂))
    functor
      = functor-square-sigma
        (SplitDependentFunctorSquare.dependent-functor s)

  split-functor-square-sigma
    : SplitDependentFunctorSquare F₂ G₂ H₁₂ H₂₂
    → SplitFunctorSquare
      (functor-sigma F₂)
      (functor-sigma G₂)
      (split-functor-sigma H₁₂)
      (split-functor-sigma H₂₂)
  split-functor-square-sigma s
    = record {SplitFunctorSquareSigma s}

