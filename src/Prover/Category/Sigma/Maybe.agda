module Prover.Category.Sigma.Maybe where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; Functor; FunctorCompose;
    FunctorIdentity; FunctorSquare)
open import Prover.Category.Maybe
  using (dependent-category-maybe; dependent-functor-compose-maybe;
    dependent-functor-identity-maybe; dependent-functor-maybe;
    dependent-functor-square-maybe)
open import Prover.Category.Sigma
  using (category-sigma; functor-compose-sigma; functor-identity-sigma;
    functor-sigma; functor-sigma₁; functor-square-sigma; functor-square-sigma₁)

-- ## Category

category-sigma-maybe
  : {C₁ : Category}
  → DependentCategory C₁
  → Category
category-sigma-maybe C₂
  = category-sigma
    (dependent-category-maybe C₂)

-- ## Functor

functor-sigma-maybe
  : {C₁ D₁ : Category}
  → {C₂ : DependentCategory C₁}
  → {D₂ : DependentCategory D₁}
  → DependentFunctor C₂ D₂
  → Functor
    (category-sigma-maybe C₂)
    (category-sigma-maybe D₂)
functor-sigma-maybe F₂
  = functor-sigma
    (dependent-functor-maybe F₂)

-- ## Functor₁

functor-sigma-maybe₁
  : {C₁ : Category}
  → (C₂ : DependentCategory C₁)
  → Functor (category-sigma-maybe C₂) C₁
functor-sigma-maybe₁ C₂
  = functor-sigma₁
    (dependent-category-maybe C₂)

-- ## FunctorIdentity

functor-identity-sigma-maybe
  : {C₁ : Category}
  → {C₂ : DependentCategory C₁}
  → {F₂ : DependentFunctor C₂ C₂}
  → DependentFunctorIdentity F₂
  → FunctorIdentity
    (functor-sigma-maybe F₂)
functor-identity-sigma-maybe p₂
  = functor-identity-sigma
    (dependent-functor-identity-maybe p₂)

-- ## FunctorCompose

functor-compose-sigma-maybe
  : {C₁ D₁ E₁ : Category}
  → {C₂ : DependentCategory C₁}
  → {D₂ : DependentCategory D₁}
  → {E₂ : DependentCategory E₁}
  → {F₂ : DependentFunctor D₂ E₂}
  → {G₂ : DependentFunctor C₂ D₂}
  → {H₂ : DependentFunctor C₂ E₂}
  → DependentFunctorCompose F₂ G₂ H₂
  → FunctorCompose
    (functor-sigma-maybe F₂)
    (functor-sigma-maybe G₂)
    (functor-sigma-maybe H₂)
functor-compose-sigma-maybe p₂
  = functor-compose-sigma
    (dependent-functor-compose-maybe p₂)

-- ## FunctorSquare

functor-square-sigma-maybe
  : {C₁₁ C₂₁ D₁₁ D₂₁ : Category}
  → {C₁₂ : DependentCategory C₁₁}
  → {C₂₂ : DependentCategory C₂₁}
  → {D₁₂ : DependentCategory D₁₁}
  → {D₂₂ : DependentCategory D₂₁}
  → {F₂ : DependentFunctor C₁₂ C₂₂}
  → {G₂ : DependentFunctor D₁₂ D₂₂}
  → {H₁₂ : DependentFunctor C₁₂ D₁₂}
  → {H₂₂ : DependentFunctor C₂₂ D₂₂}
  → DependentFunctorSquare F₂ G₂ H₁₂ H₂₂
  → FunctorSquare
    (functor-sigma-maybe F₂)
    (functor-sigma-maybe G₂)
    (functor-sigma-maybe H₁₂)
    (functor-sigma-maybe H₂₂)
functor-square-sigma-maybe s₂
  = functor-square-sigma
    (dependent-functor-square-maybe s₂)

-- ## FunctorSquare₁

functor-square-sigma-maybe₁
  : {C₁₁ C₂₁ : Category}
  → {C₁₂ : DependentCategory C₁₁}
  → {C₂₂ : DependentCategory C₂₁}
  → (F₂ : DependentFunctor C₁₂ C₂₂)
  → FunctorSquare
    (functor-sigma-maybe F₂)
    (DependentFunctor.functor F₂)
    (functor-sigma-maybe₁ C₁₂)
    (functor-sigma-maybe₁ C₂₂)
functor-square-sigma-maybe₁ F₂
  = functor-square-sigma₁
    (dependent-functor-maybe F₂)

