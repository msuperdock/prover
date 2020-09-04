module Prover.Category.Split.Sigma.Maybe where

open import Prover.Category
  using (Category)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Dependent1.Split
  using (Dependent₁SplitFunctor; Dependent₁SplitFunctorSquare)
open import Prover.Category.Dependent1.Split.Maybe
  using (dependent₁-split-functor-maybe; dependent₁-split-functor-square-maybe)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-maybe; functor-sigma-maybe)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Category.Split.Sigma
  using (split-functor-sigma; split-functor-square-sigma)

-- ## SplitFunctor

split-functor-sigma-maybe
  : {C₁ : Category}
  → {C₂ D₂ : Dependent₁Category C₁}
  → Dependent₁SplitFunctor C₂ D₂
  → SplitFunctor
    (category-sigma-maybe C₂)
    (category-sigma-maybe D₂)
split-functor-sigma-maybe F₂
  = split-functor-sigma
    (dependent₁-split-functor-maybe F₂)

-- ## SplitFunctorSquare

split-functor-square-sigma-maybe
  : {C₁₁ C₂₁ : Category}
  → {C₁₂ D₁₂ : Dependent₁Category C₁₁}
  → {C₂₂ D₂₂ : Dependent₁Category C₂₁}
  → {F₂ : Dependent₁Functor C₁₂ C₂₂}
  → {G₂ : Dependent₁Functor D₁₂ D₂₂}
  → {H₁₂ : Dependent₁SplitFunctor C₁₂ D₁₂}
  → {H₂₂ : Dependent₁SplitFunctor C₂₂ D₂₂}
  → Dependent₁SplitFunctorSquare F₂ G₂ H₁₂ H₂₂
  → SplitFunctorSquare
    (functor-sigma-maybe F₂)
    (functor-sigma-maybe G₂)
    (split-functor-sigma-maybe H₁₂)
    (split-functor-sigma-maybe H₂₂)
split-functor-square-sigma-maybe s₂
  = split-functor-square-sigma
    (dependent₁-split-functor-square-maybe s₂)

