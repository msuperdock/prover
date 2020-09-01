module Prover.Category.Split.Sigma.Maybe where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-maybe; functor-sigma-maybe)
open import Prover.Category.Split
  using (SplitDependentFunctor; SplitDependentFunctorSquare; SplitFunctor;
    SplitFunctorSquare)
open import Prover.Category.Split.Maybe
  using (split-dependent-functor-maybe; split-dependent-functor-square-maybe)
open import Prover.Category.Split.Sigma
  using (split-functor-sigma; split-functor-square-sigma)

-- ## SplitFunctor

split-functor-sigma-maybe
  : {C₁ : Category}
  → {C₂ D₂ : DependentCategory C₁}
  → SplitDependentFunctor C₂ D₂
  → SplitFunctor
    (category-sigma-maybe C₂)
    (category-sigma-maybe D₂)
split-functor-sigma-maybe F₂
  = split-functor-sigma
    (split-dependent-functor-maybe F₂)

-- ## SplitFunctorSquare

split-functor-square-sigma-maybe
  : {C₁₁ C₂₁ : Category}
  → {C₁₂ D₁₂ : DependentCategory C₁₁}
  → {C₂₂ D₂₂ : DependentCategory C₂₁}
  → {F₂ : DependentFunctor C₁₂ C₂₂}
  → {G₂ : DependentFunctor D₁₂ D₂₂}
  → {H₁₂ : SplitDependentFunctor C₁₂ D₁₂}
  → {H₂₂ : SplitDependentFunctor C₂₂ D₂₂}
  → SplitDependentFunctorSquare F₂ G₂ H₁₂ H₂₂
  → SplitFunctorSquare
    (functor-sigma-maybe F₂)
    (functor-sigma-maybe G₂)
    (split-functor-sigma-maybe H₁₂)
    (split-functor-sigma-maybe H₂₂)
split-functor-square-sigma-maybe s₂
  = split-functor-square-sigma
    (split-dependent-functor-square-maybe s₂)

