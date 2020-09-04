module Prover.Category.Sigma.Sum where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare;
    functor-compose'; functor-square-compose)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor; Dependent₁FunctorCompose;
    Dependent₁FunctorIdentity; Dependent₁FunctorSquare)
open import Prover.Category.Sigma.Maybe
  using (functor-compose-sigma-maybe; functor-identity-sigma-maybe;
    functor-sigma-maybe₁; functor-square-sigma-maybe;
    functor-square-sigma-maybe₁)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Category.Sum
  using (category-sum; functor-sum; functor-compose-sum; functor-identity-sum;
    functor-square-sum)

-- ## Category

category-sigma-sum
  : {C₁₁ C₂₁ : Category}
  → Dependent₁Category C₂₁
  → SplitFunctor C₁₁ C₂₁
  → Category
category-sigma-sum C₂₂ F₁
  = category-sum
    (functor-compose'
      (SplitFunctor.functor F₁)
      (functor-sigma-maybe₁ C₂₂))

-- ## Functor

functor-sigma-sum
  : {C₁₁ C₂₁ D₁₁ D₂₁ : Category}
  → {C₂₂ : Dependent₁Category C₂₁}
  → {D₂₂ : Dependent₁Category D₂₁}
  → {F₁ : SplitFunctor C₁₁ C₂₁}
  → {G₁ : SplitFunctor D₁₁ D₂₁}
  → {H₁₁ : Functor C₁₁ D₁₁}
  → (H₂₂ : Dependent₁Functor C₂₂ D₂₂)
  → SplitFunctorSquare H₁₁ (Dependent₁Functor.functor H₂₂) F₁ G₁
  → Functor
    (category-sigma-sum C₂₂ F₁)
    (category-sigma-sum D₂₂ G₁)
functor-sigma-sum H₂₂ s₁
  = functor-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-maybe₁ H₂₂))

-- ## FunctorIdentity

functor-identity-sigma-sum
  : {C₁₁ C₂₁ : Category}
  → {C₂₂ : Dependent₁Category C₂₁}
  → {F₁ : SplitFunctor C₁₁ C₂₁}
  → {G₁₁ : Functor C₁₁ C₁₁}
  → {G₂₂ : Dependent₁Functor C₂₂ C₂₂}
  → (s₁ : SplitFunctorSquare G₁₁ (Dependent₁Functor.functor G₂₂) F₁ F₁)
  → FunctorIdentity G₁₁
  → Dependent₁FunctorIdentity G₂₂
  → FunctorIdentity
    (functor-sigma-sum {C₂₂ = C₂₂} {D₂₂ = C₂₂} G₂₂ s₁)
functor-identity-sigma-sum {G₂₂ = G₂₂} s₁ p₁₁ p₂₂
  = functor-identity-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-maybe₁ G₂₂)) p₁₁
    (functor-identity-sigma-maybe {F₂ = G₂₂} p₂₂)

-- ## FunctorCompose

functor-compose-sigma-sum
  : {C₁₁ C₂₁ D₁₁ D₂₁ E₁₁ E₂₁ : Category}
  → {C₂₂ : Dependent₁Category C₂₁}
  → {D₂₂ : Dependent₁Category D₂₁}
  → {E₂₂ : Dependent₁Category E₂₁}
  → {I₁ : SplitFunctor C₁₁ C₂₁}
  → {J₁ : SplitFunctor D₁₁ D₂₁}
  → {K₁ : SplitFunctor E₁₁ E₂₁}
  → {L₁₁ : Functor D₁₁ E₁₁}
  → {M₁₁ : Functor C₁₁ D₁₁}
  → {N₁₁ : Functor C₁₁ E₁₁}
  → {L₂₂ : Dependent₁Functor D₂₂ E₂₂}
  → {M₂₂ : Dependent₁Functor C₂₂ D₂₂}
  → {N₂₂ : Dependent₁Functor C₂₂ E₂₂}
  → (s₁ : SplitFunctorSquare L₁₁ (Dependent₁Functor.functor L₂₂) J₁ K₁)
  → (t₁ : SplitFunctorSquare M₁₁ (Dependent₁Functor.functor M₂₂) I₁ J₁)
  → (u₁ : SplitFunctorSquare N₁₁ (Dependent₁Functor.functor N₂₂) I₁ K₁)
  → FunctorCompose L₁₁ M₁₁ N₁₁
  → Dependent₁FunctorCompose L₂₂ M₂₂ N₂₂
  → FunctorCompose
    (functor-sigma-sum {C₂₂ = D₂₂} {D₂₂ = E₂₂} L₂₂ s₁)
    (functor-sigma-sum {C₂₂ = C₂₂} {D₂₂ = D₂₂} M₂₂ t₁)
    (functor-sigma-sum {C₂₂ = C₂₂} {D₂₂ = E₂₂} N₂₂ u₁)
functor-compose-sigma-sum {L₂₂ = L₂₂} {M₂₂ = M₂₂} {N₂₂ = N₂₂} s₁ t₁ u₁ p₁₁ p₂₂
  = functor-compose-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-maybe₁ L₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor t₁)
      (functor-square-sigma-maybe₁ M₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor u₁)
      (functor-square-sigma-maybe₁ N₂₂)) p₁₁
    (functor-compose-sigma-maybe {F₂ = L₂₂} {G₂ = M₂₂} {H₂ = N₂₂} p₂₂)

-- ## FunctorSquare

functor-square-sigma-sum
  : {C₁₁₁ C₁₂₁ C₂₁₁ C₂₂₁ D₁₁₁ D₁₂₁ D₂₁₁ D₂₂₁ : Category}
  → {C₁₂₂ : Dependent₁Category C₁₂₁}
  → {C₂₂₂ : Dependent₁Category C₂₂₁}
  → {D₁₂₂ : Dependent₁Category D₁₂₁}
  → {D₂₂₂ : Dependent₁Category D₂₂₁}
  → {F₁₁ : SplitFunctor C₁₁₁ C₁₂₁}
  → {F₂₁ : SplitFunctor C₂₁₁ C₂₂₁}
  → {G₁₁ : SplitFunctor D₁₁₁ D₁₂₁}
  → {G₂₁ : SplitFunctor D₂₁₁ D₂₂₁}
  → {H₁₁ : Functor C₁₁₁ C₂₁₁}
  → {I₁₁ : Functor D₁₁₁ D₂₁₁}
  → {J₁₁₁ : Functor C₁₁₁ D₁₁₁}
  → {J₂₁₁ : Functor C₂₁₁ D₂₁₁}
  → {H₂₂ : Dependent₁Functor C₁₂₂ C₂₂₂}
  → {I₂₂ : Dependent₁Functor D₁₂₂ D₂₂₂}
  → {J₁₂₂ : Dependent₁Functor C₁₂₂ D₁₂₂}
  → {J₂₂₂ : Dependent₁Functor C₂₂₂ D₂₂₂}
  → (s₁ : SplitFunctorSquare H₁₁ (Dependent₁Functor.functor H₂₂) F₁₁ F₂₁)
  → (t₁ : SplitFunctorSquare I₁₁ (Dependent₁Functor.functor I₂₂) G₁₁ G₂₁)
  → (u₁₁ : SplitFunctorSquare J₁₁₁ (Dependent₁Functor.functor J₁₂₂) F₁₁ G₁₁)
  → (u₂₁ : SplitFunctorSquare J₂₁₁ (Dependent₁Functor.functor J₂₂₂) F₂₁ G₂₁)
  → FunctorSquare H₁₁ I₁₁ J₁₁₁ J₂₁₁
  → Dependent₁FunctorSquare H₂₂ I₂₂ J₁₂₂ J₂₂₂
  → FunctorSquare
    (functor-sigma-sum {C₂₂ = C₁₂₂} {D₂₂ = C₂₂₂} H₂₂ s₁)
    (functor-sigma-sum {C₂₂ = D₁₂₂} {D₂₂ = D₂₂₂} I₂₂ t₁)
    (functor-sigma-sum {C₂₂ = C₁₂₂} {D₂₂ = D₁₂₂} J₁₂₂ u₁₁)
    (functor-sigma-sum {C₂₂ = C₂₂₂} {D₂₂ = D₂₂₂} J₂₂₂ u₂₁)
functor-square-sigma-sum
  {H₂₂ = H₂₂} {I₂₂ = I₂₂} {J₁₂₂ = J₁₂₂} {J₂₂₂ = J₂₂₂} s₁ t₁ u₁₁ u₂₁ v₁₁ v₂₂
  = functor-square-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-maybe₁ H₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor t₁)
      (functor-square-sigma-maybe₁ I₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor u₁₁)
      (functor-square-sigma-maybe₁ J₁₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor u₂₁)
      (functor-square-sigma-maybe₁ J₂₂₂)) v₁₁
    (functor-square-sigma-maybe
      {F₂ = H₂₂} {G₂ = I₂₂} {H₁₂ = J₁₂₂} {H₂₂ = J₂₂₂} v₂₂)

