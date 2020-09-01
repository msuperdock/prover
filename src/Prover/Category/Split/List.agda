module Prover.Category.Split.List where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.List
  using (module CategoryList; category-list; functor-list)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Category.Split.Setoid
  using (split-functor-setoid; split-functor-square-setoid)
open import Prover.Category.Split.Setoid.List
  using (split-setoid-functor-list; split-setoid-functor-square-list)

-- ## SplitFunctor

split-functor-list
  : {C D : Category}
  → SplitFunctor C D
  → SplitFunctor
    (category-list C)
    (category-list D)
split-functor-list {C = C} {D = D} F
  = split-functor-setoid
    (CategoryList.Arrow C)
    (CategoryList.Arrow D)
    (CategoryList.ArrowIsomorphism C)
    (CategoryList.ArrowIsomorphism D)
    (split-setoid-functor-list F)

-- ## SplitFunctorSquare

split-functor-square-list
  : {C₁ C₂ D₁ D₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : SplitFunctor C₁ D₁}
  → {H₂ : SplitFunctor C₂ D₂}
  → SplitFunctorSquare F G H₁ H₂
  → SplitFunctorSquare
    (functor-list F)
    (functor-list G)
    (split-functor-list H₁)
    (split-functor-list H₂)
split-functor-square-list {C₁ = C₁} {C₂ = C₂} {D₁ = D₁} {D₂ = D₂} s
  = split-functor-square-setoid
    (CategoryList.Arrow C₁)
    (CategoryList.Arrow C₂)
    (CategoryList.Arrow D₁)
    (CategoryList.Arrow D₂)
    (CategoryList.ArrowIsomorphism C₁)
    (CategoryList.ArrowIsomorphism C₂)
    (CategoryList.ArrowIsomorphism D₁)
    (CategoryList.ArrowIsomorphism D₂)
    (split-setoid-functor-square-list s)

