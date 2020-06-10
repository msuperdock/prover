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
category-sigma-sum C₂ F₁
  = category-sum
    (functor-compose'
      (SplitFunctor.functor F₁)
      (functor-sigma-may₁ C₂))

-- ## Functor

functor-sigma-sum
  : {C₁₁ C₂₁ D₁₁ D₂₁ : Category}
  → {C₂ : DependentCategory C₂₁}
  → {D₂ : DependentCategory D₂₁}
  → {F₁ : SplitFunctor C₁₁ C₂₁}
  → {G₁ : SplitFunctor D₁₁ D₂₁}
  → {H₁₁ : Functor C₁₁ D₁₁}
  → (H₂ : DependentFunctor C₂ D₂)
  → SplitFunctorSquare H₁₁ (DependentFunctor.functor H₂) F₁ G₁
  → Functor
    (category-sigma-sum C₂ F₁)
    (category-sigma-sum D₂ G₁)
functor-sigma-sum H₂ s₁
  = functor-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-may₁ H₂))

-- ## FunctorIdentity

functor-identity-sigma-sum
  : {C₁₁ C₂₁ : Category}
  → {C₂ : DependentCategory C₂₁}
  → {F₁ : SplitFunctor C₁₁ C₂₁}
  → {G₁₁ : Functor C₁₁ C₁₁}
  → {G₂ : DependentFunctor C₂ C₂}
  → (s₁ : SplitFunctorSquare G₁₁ (DependentFunctor.functor G₂) F₁ F₁)
  → FunctorIdentity G₁₁
  → DependentFunctorIdentity G₂
  → FunctorIdentity
    (functor-sigma-sum {C₂ = C₂} {D₂ = C₂} G₂ s₁)
functor-identity-sigma-sum {G₂ = G₂} s₁ p₁₁ p₂
  = functor-identity-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-may₁ G₂)) p₁₁
    (functor-identity-sigma-may {F₂ = G₂} p₂)

-- ## FunctorCompose

functor-compose-sigma-sum
  : {C₁₁ C₂₁ D₁₁ D₂₁ E₁₁ E₂₁ : Category}
  → {C₂ : DependentCategory C₂₁}
  → {D₂ : DependentCategory D₂₁}
  → {E₂ : DependentCategory E₂₁}
  → {I₁ : SplitFunctor C₁₁ C₂₁}
  → {J₁ : SplitFunctor D₁₁ D₂₁}
  → {K₁ : SplitFunctor E₁₁ E₂₁}
  → {L₁₁ : Functor D₁₁ E₁₁}
  → {M₁₁ : Functor C₁₁ D₁₁}
  → {N₁₁ : Functor C₁₁ E₁₁}
  → {L₂ : DependentFunctor D₂ E₂}
  → {M₂ : DependentFunctor C₂ D₂}
  → {N₂ : DependentFunctor C₂ E₂}
  → (s₁ : SplitFunctorSquare L₁₁ (DependentFunctor.functor L₂) J₁ K₁)
  → (t₁ : SplitFunctorSquare M₁₁ (DependentFunctor.functor M₂) I₁ J₁)
  → (u₁ : SplitFunctorSquare N₁₁ (DependentFunctor.functor N₂) I₁ K₁)
  → FunctorCompose L₁₁ M₁₁ N₁₁
  → DependentFunctorCompose L₂ M₂ N₂
  → FunctorCompose
    (functor-sigma-sum {C₂ = D₂} {D₂ = E₂} L₂ s₁)
    (functor-sigma-sum {C₂ = C₂} {D₂ = D₂} M₂ t₁)
    (functor-sigma-sum {C₂ = C₂} {D₂ = E₂} N₂ u₁)
functor-compose-sigma-sum {L₂ = L₂} {M₂ = M₂} {N₂ = N₂} s₁ t₁ u₁ p₁₁ p₂
  = functor-compose-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-may₁ L₂))
    (functor-square-compose
      (SplitFunctorSquare.functor t₁)
      (functor-square-sigma-may₁ M₂))
    (functor-square-compose
      (SplitFunctorSquare.functor u₁)
      (functor-square-sigma-may₁ N₂)) p₁₁
    (functor-compose-sigma-may {F₂ = L₂} {G₂ = M₂} {H₂ = N₂} p₂)

-- ## FunctorSquare

functor-square-sigma-sum
  : {C₁₁₁ C₁₂₁ C₂₁₁ C₂₂₁ D₁₁₁ D₁₂₁ D₂₁₁ D₂₂₁ : Category}
  → {C₁₂ : DependentCategory C₁₂₁}
  → {C₂₂ : DependentCategory C₂₂₁}
  → {D₁₂ : DependentCategory D₁₂₁}
  → {D₂₂ : DependentCategory D₂₂₁}
  → {F₁₁ : SplitFunctor C₁₁₁ C₁₂₁}
  → {F₂₁ : SplitFunctor C₂₁₁ C₂₂₁}
  → {G₁₁ : SplitFunctor D₁₁₁ D₁₂₁}
  → {G₂₁ : SplitFunctor D₂₁₁ D₂₂₁}
  → {H₁₁ : Functor C₁₁₁ C₂₁₁}
  → {I₁₁ : Functor D₁₁₁ D₂₁₁}
  → {J₁₁₁ : Functor C₁₁₁ D₁₁₁}
  → {J₂₁₁ : Functor C₂₁₁ D₂₁₁}
  → {H₂ : DependentFunctor C₁₂ C₂₂}
  → {I₂ : DependentFunctor D₁₂ D₂₂}
  → {J₁₂ : DependentFunctor C₁₂ D₁₂}
  → {J₂₂ : DependentFunctor C₂₂ D₂₂}
  → (s₁ : SplitFunctorSquare H₁₁ (DependentFunctor.functor H₂) F₁₁ F₂₁)
  → (t₁ : SplitFunctorSquare I₁₁ (DependentFunctor.functor I₂) G₁₁ G₂₁)
  → (u₁₁ : SplitFunctorSquare J₁₁₁ (DependentFunctor.functor J₁₂) F₁₁ G₁₁)
  → (u₂₁ : SplitFunctorSquare J₂₁₁ (DependentFunctor.functor J₂₂) F₂₁ G₂₁)
  → FunctorSquare H₁₁ I₁₁ J₁₁₁ J₂₁₁
  → DependentFunctorSquare H₂ I₂ J₁₂ J₂₂
  → FunctorSquare
    (functor-sigma-sum {C₂ = C₁₂} {D₂ = C₂₂} H₂ s₁)
    (functor-sigma-sum {C₂ = D₁₂} {D₂ = D₂₂} I₂ t₁)
    (functor-sigma-sum {C₂ = C₁₂} {D₂ = D₁₂} J₁₂ u₁₁)
    (functor-sigma-sum {C₂ = C₂₂} {D₂ = D₂₂} J₂₂ u₂₁)
functor-square-sigma-sum
  {H₂ = H₂} {I₂ = I₂} {J₁₂ = J₁₂} {J₂₂ = J₂₂} s₁ t₁ u₁₁ u₂₁ v₁₁ v₂
  = functor-square-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-may₁ H₂))
    (functor-square-compose
      (SplitFunctorSquare.functor t₁)
      (functor-square-sigma-may₁ I₂))
    (functor-square-compose
      (SplitFunctorSquare.functor u₁₁)
      (functor-square-sigma-may₁ J₁₂))
    (functor-square-compose
      (SplitFunctorSquare.functor u₂₁)
      (functor-square-sigma-may₁ J₂₂)) v₁₁
    (functor-square-sigma-may {F₂ = H₂} {G₂ = I₂} {H₁₂ = J₁₂} {H₂₂ = J₂₂} v₂)

