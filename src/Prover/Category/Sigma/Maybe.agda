module Prover.Category.Sigma.Maybe where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor; Dependent₁FunctorCompose;
    Dependent₁FunctorIdentity; Dependent₁FunctorSquare)
open import Prover.Category.Dependent1.Maybe
  using (dependent₁-category-maybe; dependent₁-functor-compose-maybe;
    dependent₁-functor-identity-maybe; dependent₁-functor-maybe;
    dependent₁-functor-square-maybe)
open import Prover.Category.Sigma
  using (category-sigma; functor-compose-sigma; functor-identity-sigma;
    functor-sigma; functor-sigma₁; functor-square-sigma; functor-square-sigma₁)

-- ## Category

category-sigma-maybe
  : {C₁ : Category}
  → Dependent₁Category C₁
  → Category
category-sigma-maybe C₂
  = category-sigma
    (dependent₁-category-maybe C₂)

-- ## Functor

functor-sigma-maybe
  : {C₁ D₁ : Category}
  → {C₂ : Dependent₁Category C₁}
  → {D₂ : Dependent₁Category D₁}
  → {F₁ : Functor C₁ D₁}
  → Dependent₁Functor C₂ D₂ F₁
  → Functor
    (category-sigma-maybe C₂)
    (category-sigma-maybe D₂)
functor-sigma-maybe F₂
  = functor-sigma
    (dependent₁-functor-maybe F₂)

-- ## Functor₁

functor-sigma-maybe₁
  : {C₁ : Category}
  → (C₂ : Dependent₁Category C₁)
  → Functor (category-sigma-maybe C₂) C₁
functor-sigma-maybe₁ C₂
  = functor-sigma₁
    (dependent₁-category-maybe C₂)

-- ## FunctorIdentity

functor-identity-sigma-maybe
  : {C₁ : Category}
  → {C₂ : Dependent₁Category C₁}
  → {F₁ : Functor C₁ C₁}
  → {F₂ : Dependent₁Functor C₂ C₂ F₁}
  → FunctorIdentity F₁
  → Dependent₁FunctorIdentity F₂
  → FunctorIdentity
    (functor-sigma-maybe F₂)
functor-identity-sigma-maybe p₁ p₂
  = functor-identity-sigma p₁
    (dependent₁-functor-identity-maybe p₁ p₂)

-- ## FunctorCompose

functor-compose-sigma-maybe
  : {C₁ D₁ E₁ : Category}
  → {C₂ : Dependent₁Category C₁}
  → {D₂ : Dependent₁Category D₁}
  → {E₂ : Dependent₁Category E₁}
  → {F₁ : Functor D₁ E₁}
  → {G₁ : Functor C₁ D₁}
  → {H₁ : Functor C₁ E₁}
  → {F₂ : Dependent₁Functor D₂ E₂ F₁}
  → {G₂ : Dependent₁Functor C₂ D₂ G₁}
  → {H₂ : Dependent₁Functor C₂ E₂ H₁}
  → FunctorCompose F₁ G₁ H₁
  → Dependent₁FunctorCompose F₂ G₂ H₂
  → FunctorCompose
    (functor-sigma-maybe F₂)
    (functor-sigma-maybe G₂)
    (functor-sigma-maybe H₂)
functor-compose-sigma-maybe p₁ p₂
  = functor-compose-sigma p₁
    (dependent₁-functor-compose-maybe p₁ p₂)

-- ## FunctorSquare

functor-square-sigma-maybe
  : {C₁₁ C₂₁ D₁₁ D₂₁ : Category}
  → {C₁₂ : Dependent₁Category C₁₁}
  → {C₂₂ : Dependent₁Category C₂₁}
  → {D₁₂ : Dependent₁Category D₁₁}
  → {D₂₂ : Dependent₁Category D₂₁}
  → {F₁ : Functor C₁₁ C₂₁}
  → {G₁ : Functor D₁₁ D₂₁}
  → {H₁₁ : Functor C₁₁ D₁₁}
  → {H₂₁ : Functor C₂₁ D₂₁}
  → {F₂ : Dependent₁Functor C₁₂ C₂₂ F₁}
  → {G₂ : Dependent₁Functor D₁₂ D₂₂ G₁}
  → {H₁₂ : Dependent₁Functor C₁₂ D₁₂ H₁₁}
  → {H₂₂ : Dependent₁Functor C₂₂ D₂₂ H₂₁}
  → FunctorSquare F₁ G₁ H₁₁ H₂₁
  → Dependent₁FunctorSquare F₂ G₂ H₁₂ H₂₂
  → FunctorSquare
    (functor-sigma-maybe F₂)
    (functor-sigma-maybe G₂)
    (functor-sigma-maybe H₁₂)
    (functor-sigma-maybe H₂₂)
functor-square-sigma-maybe s₁ s₂
  = functor-square-sigma s₁
    (dependent₁-functor-square-maybe s₁ s₂)

-- ## FunctorSquare₁

functor-square-sigma-maybe₁
  : {C₁₁ C₂₁ : Category}
  → {C₁₂ : Dependent₁Category C₁₁}
  → {C₂₂ : Dependent₁Category C₂₁}
  → {F₁ : Functor C₁₁ C₂₁}
  → (F₂ : Dependent₁Functor C₁₂ C₂₂ F₁)
  → FunctorSquare
    (functor-sigma-maybe F₂) F₁
    (functor-sigma-maybe₁ C₁₂)
    (functor-sigma-maybe₁ C₂₂)
functor-square-sigma-maybe₁ F₂
  = functor-square-sigma₁
    (dependent₁-functor-maybe F₂)

