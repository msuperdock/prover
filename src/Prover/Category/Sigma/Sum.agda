module Prover.Category.Sigma.Sum where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; Functor; FunctorCompose;
    FunctorIdentity; FunctorSquare; functor-compose'; functor-square-compose)
open import Prover.Category.Sigma.Maybe
  using (functor-compose-sigma-may; functor-identity-sigma-may;
    functor-sigma-may₁; functor-square-sigma-may; functor-square-sigma-may₁)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Category.Sum
  using (category-sum; functor-sum; functor-compose-sum; functor-identity-sum;
    functor-square-sum)
open import Prover.Prelude

-- ## Category

category-sigma-sum
  : {C₁₁ C₂₁ : Category}
  → DependentCategory C₂₁
  → SplitFunctor C₁₁ C₂₁
  → Category
category-sigma-sum C₂₂ F₁
  = category-sum
    (functor-compose'
      (SplitFunctor.functor F₁)
      (functor-sigma-may₁ C₂₂))

-- ## Functor

functor-sigma-sum
  : {C₁₁ C₂₁ D₁₁ D₂₁ : Category}
  → {C₂₂ : DependentCategory C₂₁}
  → {D₂₂ : DependentCategory D₂₁}
  → {F₁ : SplitFunctor C₁₁ C₂₁}
  → {G₁ : SplitFunctor D₁₁ D₂₁}
  → {H₁₁ : Functor C₁₁ D₁₁}
  → (H₂₂ : DependentFunctor C₂₂ D₂₂)
  → SplitFunctorSquare H₁₁ (DependentFunctor.functor H₂₂) F₁ G₁
  → Functor
    (category-sigma-sum C₂₂ F₁)
    (category-sigma-sum D₂₂ G₁)
functor-sigma-sum H₂₂ s₁
  = functor-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-may₁ H₂₂))

-- ## FunctorIdentity

functor-identity-sigma-sum
  : {C₁₁ C₂₁ : Category}
  → {C₂₂ : DependentCategory C₂₁}
  → {F₁ : SplitFunctor C₁₁ C₂₁}
  → {G₁₁ : Functor C₁₁ C₁₁}
  → {G₂₂ : DependentFunctor C₂₂ C₂₂}
  → (s₁ : SplitFunctorSquare G₁₁ (DependentFunctor.functor G₂₂) F₁ F₁)
  → FunctorIdentity G₁₁
  → DependentFunctorIdentity G₂₂
  → FunctorIdentity
    (functor-sigma-sum {C₂₂ = C₂₂} {D₂₂ = C₂₂} G₂₂ s₁)
functor-identity-sigma-sum {G₂₂ = G₂₂} s₁ p₁₁ p₂₂
  = functor-identity-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-may₁ G₂₂)) p₁₁
    (functor-identity-sigma-may {F₂ = G₂₂} p₂₂)

-- ## FunctorCompose

functor-compose-sigma-sum
  : {C₁₁ C₂₁ D₁₁ D₂₁ E₁₁ E₂₁ : Category}
  → {C₂₂ : DependentCategory C₂₁}
  → {D₂₂ : DependentCategory D₂₁}
  → {E₂₂ : DependentCategory E₂₁}
  → {I₁ : SplitFunctor C₁₁ C₂₁}
  → {J₁ : SplitFunctor D₁₁ D₂₁}
  → {K₁ : SplitFunctor E₁₁ E₂₁}
  → {L₁₁ : Functor D₁₁ E₁₁}
  → {M₁₁ : Functor C₁₁ D₁₁}
  → {N₁₁ : Functor C₁₁ E₁₁}
  → {L₂₂ : DependentFunctor D₂₂ E₂₂}
  → {M₂₂ : DependentFunctor C₂₂ D₂₂}
  → {N₂₂ : DependentFunctor C₂₂ E₂₂}
  → (s₁ : SplitFunctorSquare L₁₁ (DependentFunctor.functor L₂₂) J₁ K₁)
  → (t₁ : SplitFunctorSquare M₁₁ (DependentFunctor.functor M₂₂) I₁ J₁)
  → (u₁ : SplitFunctorSquare N₁₁ (DependentFunctor.functor N₂₂) I₁ K₁)
  → FunctorCompose L₁₁ M₁₁ N₁₁
  → DependentFunctorCompose L₂₂ M₂₂ N₂₂
  → FunctorCompose
    (functor-sigma-sum {C₂₂ = D₂₂} {D₂₂ = E₂₂} L₂₂ s₁)
    (functor-sigma-sum {C₂₂ = C₂₂} {D₂₂ = D₂₂} M₂₂ t₁)
    (functor-sigma-sum {C₂₂ = C₂₂} {D₂₂ = E₂₂} N₂₂ u₁)
functor-compose-sigma-sum {L₂₂ = L₂₂} {M₂₂ = M₂₂} {N₂₂ = N₂₂} s₁ t₁ u₁ p₁₁ p₂₂
  = functor-compose-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-may₁ L₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor t₁)
      (functor-square-sigma-may₁ M₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor u₁)
      (functor-square-sigma-may₁ N₂₂)) p₁₁
    (functor-compose-sigma-may {F₂ = L₂₂} {G₂ = M₂₂} {H₂ = N₂₂} p₂₂)

-- ## FunctorSquare

functor-square-sigma-sum
  : {C₁₁₁ C₁₂₁ C₂₁₁ C₂₂₁ D₁₁₁ D₁₂₁ D₂₁₁ D₂₂₁ : Category}
  → {C₁₂₂ : DependentCategory C₁₂₁}
  → {C₂₂₂ : DependentCategory C₂₂₁}
  → {D₁₂₂ : DependentCategory D₁₂₁}
  → {D₂₂₂ : DependentCategory D₂₂₁}
  → {F₁₁ : SplitFunctor C₁₁₁ C₁₂₁}
  → {F₂₁ : SplitFunctor C₂₁₁ C₂₂₁}
  → {G₁₁ : SplitFunctor D₁₁₁ D₁₂₁}
  → {G₂₁ : SplitFunctor D₂₁₁ D₂₂₁}
  → {H₁₁ : Functor C₁₁₁ C₂₁₁}
  → {I₁₁ : Functor D₁₁₁ D₂₁₁}
  → {J₁₁₁ : Functor C₁₁₁ D₁₁₁}
  → {J₂₁₁ : Functor C₂₁₁ D₂₁₁}
  → {H₂₂ : DependentFunctor C₁₂₂ C₂₂₂}
  → {I₂₂ : DependentFunctor D₁₂₂ D₂₂₂}
  → {J₁₂₂ : DependentFunctor C₁₂₂ D₁₂₂}
  → {J₂₂₂ : DependentFunctor C₂₂₂ D₂₂₂}
  → (s₁ : SplitFunctorSquare H₁₁ (DependentFunctor.functor H₂₂) F₁₁ F₂₁)
  → (t₁ : SplitFunctorSquare I₁₁ (DependentFunctor.functor I₂₂) G₁₁ G₂₁)
  → (u₁₁ : SplitFunctorSquare J₁₁₁ (DependentFunctor.functor J₁₂₂) F₁₁ G₁₁)
  → (u₂₁ : SplitFunctorSquare J₂₁₁ (DependentFunctor.functor J₂₂₂) F₂₁ G₂₁)
  → FunctorSquare H₁₁ I₁₁ J₁₁₁ J₂₁₁
  → DependentFunctorSquare H₂₂ I₂₂ J₁₂₂ J₂₂₂
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
      (functor-square-sigma-may₁ H₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor t₁)
      (functor-square-sigma-may₁ I₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor u₁₁)
      (functor-square-sigma-may₁ J₁₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor u₂₁)
      (functor-square-sigma-may₁ J₂₂₂)) v₁₁
    (functor-square-sigma-may
      {F₂ = H₂₂} {G₂ = I₂₂} {H₁₂ = J₁₂₂} {H₂₂ = J₂₂₂} v₂₂)

