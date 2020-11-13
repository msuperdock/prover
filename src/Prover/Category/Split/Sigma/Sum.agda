module Prover.Category.Split.Sigma.Sum where

open import Prover.Category
  using (Category; Functor; functor-square-compose)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Dependent1.Split
  using (Dependent₁SplitFunctor; Dependent₁SplitFunctorSquare)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-maybe; functor-sigma-maybe; functor-square-sigma-maybe₁)
open import Prover.Category.Sigma.Sum
  using (category-sigma-sum; functor-sigma-sum)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare; split-functor-compose;
    split-functor-square-compose; split-functor-square-weak; split-functor-weak)
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
  → {C₂ D₂ : Dependent₁Category D₁}
  → (F₁ : SplitFunctor C₁ D₁)
  → Dependent₁SplitFunctor C₂ D₂
  → SplitFunctor
    (category-sigma-sum C₂ F₁)
    (category-sigma-maybe D₂)
split-functor-sigma-sum {C₂ = C₂} F₁ F₂
  = split-functor-compose
    (split-functor-sigma-maybe F₂)
    (split-functor-sum₂
      (weak-functor-compose
        (weak-functor-sigma-maybe₁ C₂)
        (split-functor-weak F₁)))

-- ## SplitFunctorSquare

split-functor-square-sigma-sum
  : {C₁₁ C₂₁ D₁₁ D₂₁ : Category}
  → {C₁₂ D₁₂ : Dependent₁Category D₁₁}
  → {C₂₂ D₂₂ : Dependent₁Category D₂₁}
  → {F₁ : Functor C₁₁ C₂₁}
  → {G₁ : Functor D₁₁ D₂₁}
  → {F₂ : Dependent₁Functor C₁₂ C₂₂ G₁}
  → {G₂ : Dependent₁Functor D₁₂ D₂₂ G₁}
  → {H₁₁ : SplitFunctor C₁₁ D₁₁}
  → {H₂₁ : SplitFunctor C₂₁ D₂₁}
  → {H₁₂ : Dependent₁SplitFunctor C₁₂ D₁₂}
  → {H₂₂ : Dependent₁SplitFunctor C₂₂ D₂₂}
  → (s₁ : SplitFunctorSquare F₁ G₁ H₁₁ H₂₁)
  → Dependent₁SplitFunctorSquare F₂ G₂ H₁₂ H₂₂
  → SplitFunctorSquare
    (functor-sigma-sum F₂ s₁)
    (functor-sigma-maybe G₂)
    (split-functor-sigma-sum H₁₁ H₁₂)
    (split-functor-sigma-sum H₂₁ H₂₂)
split-functor-square-sigma-sum {F₂ = F₂} s₁ s₂
  = split-functor-square-compose
    (split-functor-square-sigma-maybe s₂)
    (split-functor-square-sum₂
      (functor-square-compose
        (SplitFunctorSquare.functor s₁)
        (functor-square-sigma-maybe₁ F₂))
      (weak-functor-square-compose
        (functor-square-sigma-maybe₁ F₂)
        (SplitFunctorSquare.functor s₁)
        (weak-functor-square-sigma-maybe₁ F₂)
        (split-functor-square-weak s₁)))

