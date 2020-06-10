module Prover.Category.Split.Sigma.Maybe where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-may; functor-sigma-may)
open import Prover.Category.Split
  using (SplitDependentFunctor; SplitDependentFunctorSquare; SplitFunctor;
    SplitFunctorSquare)
open import Prover.Category.Split.Maybe
  using (split-dependent-functor-maybe; split-dependent-functor-square-maybe)
open import Prover.Category.Split.Sigma
  using (split-functor-sigma; split-functor-square-sigma)
open import Prover.Prelude

-- ## SplitFunctor

split-functor-sigma-may
  : {C₁ : Category}
  → {C₂ D₂ : DependentCategory C₁}
  → SplitDependentFunctor C₂ D₂
  → SplitFunctor
    (category-sigma-may C₂)
    (category-sigma-may D₂)
split-functor-sigma-may F₂
  = split-functor-sigma
    (split-dependent-functor-maybe F₂)

-- ## SplitFunctorSquare

split-functor-square-sigma-may
  : {C₁₁ C₂₁ : Category}
  → {C₁₂ D₁₂ : DependentCategory C₁₁}
  → {C₂₂ D₂₂ : DependentCategory C₂₁}
  → {F₂ : DependentFunctor C₁₂ C₂₂}
  → {G₂ : DependentFunctor D₁₂ D₂₂}
  → {H₁₂ : SplitDependentFunctor C₁₂ D₁₂}
  → {H₂₂ : SplitDependentFunctor C₂₂ D₂₂}
  → SplitDependentFunctorSquare F₂ G₂ H₁₂ H₂₂
  → SplitFunctorSquare
    (functor-sigma-may F₂)
    (functor-sigma-may G₂)
    (split-functor-sigma-may H₁₂)
    (split-functor-sigma-may H₂₂)
split-functor-square-sigma-may s₂
  = split-functor-square-sigma
    (split-dependent-functor-square-maybe s₂)

