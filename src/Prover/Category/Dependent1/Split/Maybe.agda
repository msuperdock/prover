module Prover.Category.Dependent1.Split.Maybe where

open import Prover.Category
  using (Category; FunctorEqual)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Dependent1.Maybe
  using (dependent₁-category-maybe; dependent₁-functor-maybe)
open import Prover.Category.Dependent1.Split
  using (Dependent₁SplitFunctor; Dependent₁SplitFunctorSquare)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare; SplitFunctorSquare')
open import Prover.Category.Split.Maybe
  using (split-functor-maybe; split-functor-square-maybe;
    split-functor-square-maybe')

-- ## Dependent₁SplitFunctor

module _
  {C : Category}
  {C' D' : Dependent₁Category C}
  where

  module Dependent₁SplitFunctorMaybe
    (F : Dependent₁SplitFunctor C' D')
    where

    split-functor
      : (x : Category.Object C)
      → SplitFunctor
        (Dependent₁Category.category (dependent₁-category-maybe C') x)
        (Dependent₁Category.category (dependent₁-category-maybe D') x)
    split-functor x
      = split-functor-maybe
        (Dependent₁SplitFunctor.split-functor F x)

    abstract

      split-functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → SplitFunctorSquare
          (Dependent₁Category.functor (dependent₁-category-maybe C') f)
          (Dependent₁Category.functor (dependent₁-category-maybe D') f)
          (split-functor x)
          (split-functor y)
      split-functor-square f
        = split-functor-square-maybe
          (Dependent₁SplitFunctor.split-functor-square F f)

  dependent₁-split-functor-maybe
    : Dependent₁SplitFunctor C' D'
    → Dependent₁SplitFunctor
      (dependent₁-category-maybe C')
      (dependent₁-category-maybe D')
  dependent₁-split-functor-maybe F
    = record {Dependent₁SplitFunctorMaybe F}

-- ## Dependent₁SplitFunctorSquare

module _
  {C₁ C₂ : Category}
  {C₁' D₁' : Dependent₁Category C₁}
  {C₂' D₂' : Dependent₁Category C₂}
  {F : Dependent₁Functor C₁' C₂'}
  {G : Dependent₁Functor D₁' D₂'}
  {H₁ : Dependent₁SplitFunctor C₁' D₁'}
  {H₂ : Dependent₁SplitFunctor C₂' D₂'}
  where

  module Dependent₁SplitFunctorSquareMaybe
    (s : Dependent₁SplitFunctorSquare F G H₁ H₂)
    where

    functor
      : FunctorEqual
        (Dependent₁Functor.functor
          (dependent₁-functor-maybe F))
        (Dependent₁Functor.functor
          (dependent₁-functor-maybe G))
    functor
      = Dependent₁SplitFunctorSquare.functor s

    split-functor
      : (x₁ : Category.Object C₁)
      → SplitFunctorSquare'
        (Dependent₁Functor.functor'
          (dependent₁-functor-maybe F) x₁)
        (Dependent₁Functor.functor'
          (dependent₁-functor-maybe G) x₁)
        (Dependent₁SplitFunctor.split-functor
          (dependent₁-split-functor-maybe H₁) x₁)
        (Dependent₁SplitFunctor.split-functor
          (dependent₁-split-functor-maybe H₂)
          (Dependent₁Functor.base (dependent₁-functor-maybe F) x₁))
    split-functor x₁
      = split-functor-square-maybe'
        (Dependent₁SplitFunctorSquare.split-functor s x₁)

  dependent₁-split-functor-square-maybe
    : Dependent₁SplitFunctorSquare F G H₁ H₂
    → Dependent₁SplitFunctorSquare
      (dependent₁-functor-maybe F)
      (dependent₁-functor-maybe G)
      (dependent₁-split-functor-maybe H₁)
      (dependent₁-split-functor-maybe H₂)
  dependent₁-split-functor-square-maybe s
    = record {Dependent₁SplitFunctorSquareMaybe s}
  
