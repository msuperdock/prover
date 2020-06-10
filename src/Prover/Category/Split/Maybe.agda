module Prover.Category.Split.Maybe where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; Functor; FunctorEqual;
    FunctorSquare)
open import Prover.Category.Maybe
  using (category-maybe; dependent-category-maybe; dependent-functor-maybe;
    functor-maybe; functor-square-maybe)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Partial.Maybe
  using (partial-functor-maybe; partial-functor-square-maybe)
open import Prover.Category.Split
  using (SplitDependentFunctor; SplitDependentFunctorSquare; SplitFunctor;
    SplitFunctorSquare; SplitFunctorSquare'; split-functor-square')
open import Prover.Prelude

-- ## SplitFunctor

module _
  {C D : Category}
  where

  module SplitFunctorMaybe
    (F : SplitFunctor C D)
    where
  
    partial-functor
      : PartialFunctor
        (category-maybe C)
        (category-maybe D)
    partial-functor
      = partial-functor-maybe
        (SplitFunctor.partial-functor F)

    open PartialFunctor partial-functor

    functor
      : Functor
        (category-maybe D)
        (category-maybe C)
    functor
      = functor-maybe
        (SplitFunctor.functor F)

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      ; map-identity
        to unmap-identity
      ; map-compose
        to unmap-compose
      )

    abstract

      base-unbase
        : (x' : Category.Object (category-maybe D))
        → base (unbase x') ≡ just x'
      base-unbase x'
        = SplitFunctor.base-unbase F x'
  
      map-unmap
        : {x' y' : Category.Object (category-maybe D)}
        → (f' : Category.Arrow (category-maybe D) x' y')
        → map (base-unbase x') (base-unbase y') (unmap f') ≡ f'
      map-unmap nothing
        = refl
      map-unmap (just f')
        = sub just (SplitFunctor.map-unmap F f')

      normalize-arrow
        : {x' : Category.Object (category-maybe D)}
        → (x : Category.Object (category-maybe C))
        → base x ≡ just x'
        → Category.Arrow (category-maybe C) x (unbase x')
      normalize-arrow x p
        = just (SplitFunctor.normalize-arrow F x p)

      normalize-valid
        : {x' : Category.Object (category-maybe D)}
        → (x : Category.Object (category-maybe C))
        → (p : base x ≡ just x')
        → map p (base-unbase x') (normalize-arrow x p)
          ≡ Category.identity (category-maybe D) x'
      normalize-valid x p
        = sub just (SplitFunctor.normalize-valid F x p)

  split-functor-maybe
    : SplitFunctor C D
    → SplitFunctor
      (category-maybe C)
      (category-maybe D)
  split-functor-maybe F
    = record {SplitFunctorMaybe F}

-- ## SplitFunctorSquare

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : SplitFunctor C₁ D₁}
  {H₂ : SplitFunctor C₂ D₂}
  where

  module SplitFunctorSquareMaybe
    (s : SplitFunctorSquare F G H₁ H₂)
    where

    partial-functor 
      : PartialFunctorSquare
        (functor-maybe F)
        (functor-maybe G)
        (SplitFunctor.partial-functor (split-functor-maybe H₁))
        (SplitFunctor.partial-functor (split-functor-maybe H₂))
    partial-functor
      = partial-functor-square-maybe
        (SplitFunctorSquare.partial-functor s)

    functor
      : FunctorSquare
        (functor-maybe G)
        (functor-maybe F)
        (SplitFunctor.functor (split-functor-maybe H₁))
        (SplitFunctor.functor (split-functor-maybe H₂))
    functor
      = functor-square-maybe
        (SplitFunctorSquare.functor s)

  split-functor-square-maybe
    : SplitFunctorSquare F G H₁ H₂
    → SplitFunctorSquare
      (functor-maybe F)
      (functor-maybe G)
      (split-functor-maybe H₁)
      (split-functor-maybe H₂)
  split-functor-square-maybe s
    = record {SplitFunctorSquareMaybe s}

-- ## SplitFunctorSquare'

split-functor-square-maybe'
  : {C₁ C₂ D₁ D₂ D₃ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₃}
  → {H₁ : SplitFunctor C₁ D₁}
  → {H₂ : SplitFunctor C₂ D₂}
  → SplitFunctorSquare' F G H₁ H₂
  → SplitFunctorSquare'
    (functor-maybe F)
    (functor-maybe G)
    (split-functor-maybe H₁)
    (split-functor-maybe H₂)
split-functor-square-maybe' (split-functor-square' s)
  = split-functor-square' (split-functor-square-maybe s)

-- ## SplitDependentFunctor

module _
  {C : Category}
  {C' D' : DependentCategory C}
  where

  module SplitDependentFunctorMaybe
    (F : SplitDependentFunctor C' D')
    where

    split-functor
      : (x : Category.Object C)
      → SplitFunctor
        (DependentCategory.category (dependent-category-maybe C') x)
        (DependentCategory.category (dependent-category-maybe D') x)
    split-functor x
      = split-functor-maybe
        (SplitDependentFunctor.split-functor F x)

    abstract

      split-functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → SplitFunctorSquare
          (DependentCategory.functor (dependent-category-maybe C') f)
          (DependentCategory.functor (dependent-category-maybe D') f)
          (split-functor x)
          (split-functor y)
      split-functor-square f
        = split-functor-square-maybe
          (SplitDependentFunctor.split-functor-square F f)

  split-dependent-functor-maybe
    : SplitDependentFunctor C' D'
    → SplitDependentFunctor
      (dependent-category-maybe C')
      (dependent-category-maybe D')
  split-dependent-functor-maybe F
    = record {SplitDependentFunctorMaybe F}

-- ## SplitDependentFunctorSquare

module _
  {C₁ C₂ : Category}
  {C₁' D₁' : DependentCategory C₁}
  {C₂' D₂' : DependentCategory C₂}
  {F : DependentFunctor C₁' C₂'}
  {G : DependentFunctor D₁' D₂'}
  {H₁ : SplitDependentFunctor C₁' D₁'}
  {H₂ : SplitDependentFunctor C₂' D₂'}
  where

  module SplitDependentFunctorSquareMaybe
    (s : SplitDependentFunctorSquare F G H₁ H₂)
    where

    functor
      : FunctorEqual
        (DependentFunctor.functor
          (dependent-functor-maybe F))
        (DependentFunctor.functor
          (dependent-functor-maybe G))
    functor
      = SplitDependentFunctorSquare.functor s

    split-functor
      : (x₁ : Category.Object C₁)
      → SplitFunctorSquare'
        (DependentFunctor.functor'
          (dependent-functor-maybe F) x₁)
        (DependentFunctor.functor'
          (dependent-functor-maybe G) x₁)
        (SplitDependentFunctor.split-functor
          (split-dependent-functor-maybe H₁) x₁)
        (SplitDependentFunctor.split-functor
          (split-dependent-functor-maybe H₂)
          (DependentFunctor.base (dependent-functor-maybe F) x₁))
    split-functor x₁
      = split-functor-square-maybe'
        (SplitDependentFunctorSquare.split-functor s x₁)

  split-dependent-functor-square-maybe
    : SplitDependentFunctorSquare F G H₁ H₂
    → SplitDependentFunctorSquare
      (dependent-functor-maybe F)
      (dependent-functor-maybe G)
      (split-dependent-functor-maybe H₁)
      (split-dependent-functor-maybe H₂)
  split-dependent-functor-square-maybe s
    = record {SplitDependentFunctorSquareMaybe s}
  
