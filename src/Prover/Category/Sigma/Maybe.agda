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
open import Prover.Prelude

-- ## Category

category-sigma-may
  : {C₁ : Category}
  → (C₂ : DependentCategory C₁)
  → Category
category-sigma-may C₂
  = category-sigma
    (dependent-category-maybe C₂)

-- ## Functor

functor-sigma-may
  : {C₁ D₁ : Category}
  → {C₂ : DependentCategory C₁}
  → {D₂ : DependentCategory D₁}
  → DependentFunctor C₂ D₂
  → Functor
    (category-sigma-may C₂)
    (category-sigma-may D₂)
functor-sigma-may F₂
  = functor-sigma
    (dependent-functor-maybe F₂)

-- ## Functor₁

functor-sigma-may₁
  : {C₁ : Category}
  → (C₂ : DependentCategory C₁)
  → Functor (category-sigma-may C₂) C₁
functor-sigma-may₁ C₂
  = functor-sigma₁
    (dependent-category-maybe C₂)

-- ## FunctorIdentity

functor-identity-sigma-may
  : {C₁ : Category}
  → {C₂ : DependentCategory C₁}
  → {F₂ : DependentFunctor C₂ C₂}
  → DependentFunctorIdentity F₂
  → FunctorIdentity
    (functor-sigma-may F₂)
functor-identity-sigma-may p₂
  = functor-identity-sigma
    (dependent-functor-identity-maybe p₂)

-- ## FunctorCompose

functor-compose-sigma-may
  : {C₁ D₁ E₁ : Category}
  → {C₂ : DependentCategory C₁}
  → {D₂ : DependentCategory D₁}
  → {E₂ : DependentCategory E₁}
  → {F₂ : DependentFunctor D₂ E₂}
  → {G₂ : DependentFunctor C₂ D₂}
  → {H₂ : DependentFunctor C₂ E₂}
  → DependentFunctorCompose F₂ G₂ H₂
  → FunctorCompose
    (functor-sigma-may F₂)
    (functor-sigma-may G₂)
    (functor-sigma-may H₂)
functor-compose-sigma-may p₂
  = functor-compose-sigma
    (dependent-functor-compose-maybe p₂)

-- ## FunctorSquare

functor-square-sigma-may
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
    (functor-sigma-may F₂)
    (functor-sigma-may G₂)
    (functor-sigma-may H₁₂)
    (functor-sigma-may H₂₂)
functor-square-sigma-may s₂
  = functor-square-sigma
    (dependent-functor-square-maybe s₂)

-- ## FunctorSquare₁

functor-square-sigma-may₁
  : {C₁₁ C₂₁ : Category}
  → {C₁₂ : DependentCategory C₁₁}
  → {C₂₂ : DependentCategory C₂₁}
  → (F₂ : DependentFunctor C₁₂ C₂₂)
  → FunctorSquare
    (functor-sigma-may F₂)
    (DependentFunctor.functor F₂)
    (functor-sigma-may₁ C₁₂)
    (functor-sigma-may₁ C₂₂)
functor-square-sigma-may₁ F₂
  = functor-square-sigma₁
    (dependent-functor-maybe F₂)

