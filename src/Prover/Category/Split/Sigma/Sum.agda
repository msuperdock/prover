module Prover.Category.Split.Sigma.Sum where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; Functor)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-maybe; functor-sigma-maybe)
open import Prover.Category.Sigma.Sum
  using (category-sigma-sum; functor-sigma-sum)
open import Prover.Category.Split
  using (SplitDependentFunctor; SplitDependentFunctorSquare; SplitFunctor;
    SplitFunctorSquare; split-functor-weak; split-functor-square-weak)
open import Prover.Category.Split.Sigma.Maybe
  using (split-functor-sigma-maybe; split-functor-square-sigma-maybe)
open import Prover.Category.Split.Sum
  using (split-functor-sum₂; split-functor-square-sum₂)
open import Prover.Category.Weak
  using (weak-functor-compose; weak-functor-square-compose)
open import Prover.Category.Weak.Sigma.Maybe
  using (weak-functor-sigma-maybe₁; weak-functor-square-sigma-maybe₁)

-- ## SplitFunctor

split-functor-sigma-sum
  : {C₁ D₁ : Category}
  → {C₂ D₂ : DependentCategory D₁}
  → (F₁ : SplitFunctor C₁ D₁)
  → SplitDependentFunctor C₂ D₂
  → SplitFunctor
    (category-sigma-sum C₂ F₁)
    (category-sigma-maybe D₂)
split-functor-sigma-sum {C₂ = C₂} F₁ F₂
  = split-functor-sum₂
    (weak-functor-compose
      (weak-functor-sigma-maybe₁ C₂)
      (split-functor-weak F₁))
    (split-functor-sigma-maybe F₂)

-- ## SplitFunctorSquare

split-functor-square-sigma-sum
  : {C₁₁ C₂₁ D₁₁ D₂₁ : Category}
  → {C₁₂ D₁₂ : DependentCategory D₁₁}
  → {C₂₂ D₂₂ : DependentCategory D₂₁}
  → {F₁ : Functor C₁₁ C₂₁}
  → {F₂ : DependentFunctor C₁₂ C₂₂}
  → {G₂ : DependentFunctor D₁₂ D₂₂}
  → {H₁₁ : SplitFunctor C₁₁ D₁₁}
  → {H₂₁ : SplitFunctor C₂₁ D₂₁}
  → {H₁₂ : SplitDependentFunctor C₁₂ D₁₂}
  → {H₂₂ : SplitDependentFunctor C₂₂ D₂₂}
  → (s₁ : SplitFunctorSquare F₁ (DependentFunctor.functor F₂) H₁₁ H₂₁)
  → SplitDependentFunctorSquare F₂ G₂ H₁₂ H₂₂
  → SplitFunctorSquare
    (functor-sigma-sum {C₂₂ = C₁₂} {D₂₂ = C₂₂} F₂ s₁)
    (functor-sigma-maybe G₂)
    (split-functor-sigma-sum {C₂ = C₁₂} {D₂ = D₁₂} H₁₁ H₁₂)
    (split-functor-sigma-sum {C₂ = C₂₂} {D₂ = D₂₂} H₂₁ H₂₂)
split-functor-square-sigma-sum {F₂ = F₂} s₁ s₂
  = split-functor-square-sum₂
    (weak-functor-square-compose
      (weak-functor-square-sigma-maybe₁ F₂)
      (split-functor-square-weak s₁))
    (split-functor-square-sigma-maybe s₂)

