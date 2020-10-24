module Prover.Category.Sigma.Sum where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare; functor-compose'; functor-square-compose)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor; Dependent₁FunctorCompose;
    Dependent₁FunctorEqual; Dependent₁FunctorIdentity; Dependent₁FunctorSquare)
open import Prover.Category.Sigma.Maybe
  using (functor-compose-sigma-maybe; functor-equal-sigma-maybe;
    functor-identity-sigma-maybe; functor-sigma-maybe₁;
    functor-square-sigma-maybe; functor-square-sigma-maybe₁)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Category.Sum
  using (category-sum; functor-sum; functor-compose-sum; functor-equal-sum;
    functor-identity-sum; functor-square-sum)

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
  → {H₂₁ : Functor C₂₁ D₂₁}
  → Dependent₁Functor C₂₂ D₂₂ H₂₁
  → SplitFunctorSquare H₁₁ H₂₁ F₁ G₁
  → Functor
    (category-sigma-sum C₂₂ F₁)
    (category-sigma-sum D₂₂ G₁)
functor-sigma-sum H₂₂ s₁
  = functor-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-maybe₁ H₂₂))

-- ## FunctorEqual

functor-equal-sigma-sum
  : {C₁₁ C₂₁ D₁₁ D₂₁ : Category}
  → {C₂₂ : Dependent₁Category C₂₁}
  → {D₂₂ : Dependent₁Category D₂₁}
  → {F₁ : SplitFunctor C₁₁ C₂₁}
  → {G₁ : SplitFunctor D₁₁ D₂₁}
  → {H₁₁₁ H₂₁₁ : Functor C₁₁ D₁₁}
  → {H₁₂₁ H₂₂₁ : Functor C₂₁ D₂₁}
  → {H₁₂₂ : Dependent₁Functor C₂₂ D₂₂ H₁₂₁}
  → {H₂₂₂ : Dependent₁Functor C₂₂ D₂₂ H₂₂₁}
  → (s₁₁ : SplitFunctorSquare H₁₁₁ H₁₂₁ F₁ G₁)
  → (s₂₁ : SplitFunctorSquare H₂₁₁ H₂₂₁ F₁ G₁)
  → FunctorEqual H₁₁₁ H₂₁₁
  → FunctorEqual H₁₂₁ H₂₂₁
  → Dependent₁FunctorEqual H₁₂₂ H₂₂₂
  → FunctorEqual
    (functor-sigma-sum H₁₂₂ s₁₁)
    (functor-sigma-sum H₂₂₂ s₂₁)
functor-equal-sigma-sum {H₁₂₂ = H₁₂₂} {H₂₂₂ = H₂₂₂} s₁₁ s₂₁ p₁₁ p₂₁ p₂₂
  = functor-equal-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁₁)
      (functor-square-sigma-maybe₁ H₁₂₂))
    (functor-square-compose
      (SplitFunctorSquare.functor s₂₁)
      (functor-square-sigma-maybe₁ H₂₂₂)) p₁₁
    (functor-equal-sigma-maybe p₂₁ p₂₂)

-- ## FunctorIdentity

functor-identity-sigma-sum
  : {C₁₁ C₂₁ : Category}
  → {C₂₂ : Dependent₁Category C₂₁}
  → {F₁ : SplitFunctor C₁₁ C₂₁}
  → {G₁₁ : Functor C₁₁ C₁₁}
  → {G₂₁ : Functor C₂₁ C₂₁}
  → {G₂₂ : Dependent₁Functor C₂₂ C₂₂ G₂₁}
  → (s₁ : SplitFunctorSquare G₁₁ G₂₁ F₁ F₁)
  → FunctorIdentity G₁₁
  → FunctorIdentity G₂₁
  → Dependent₁FunctorIdentity G₂₂
  → FunctorIdentity
    (functor-sigma-sum G₂₂ s₁)
functor-identity-sigma-sum {G₂₂ = G₂₂} s₁ p₁₁ p₂₁ p₂₂
  = functor-identity-sum
    (functor-square-compose
      (SplitFunctorSquare.functor s₁)
      (functor-square-sigma-maybe₁ G₂₂)) p₁₁
    (functor-identity-sigma-maybe p₂₁ p₂₂)

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
  → {L₂₁ : Functor D₂₁ E₂₁}
  → {M₁₁ : Functor C₁₁ D₁₁}
  → {M₂₁ : Functor C₂₁ D₂₁}
  → {N₁₁ : Functor C₁₁ E₁₁}
  → {N₂₁ : Functor C₂₁ E₂₁}
  → {L₂₂ : Dependent₁Functor D₂₂ E₂₂ L₂₁}
  → {M₂₂ : Dependent₁Functor C₂₂ D₂₂ M₂₁}
  → {N₂₂ : Dependent₁Functor C₂₂ E₂₂ N₂₁}
  → (s₁ : SplitFunctorSquare L₁₁ L₂₁ J₁ K₁)
  → (t₁ : SplitFunctorSquare M₁₁ M₂₁ I₁ J₁)
  → (u₁ : SplitFunctorSquare N₁₁ N₂₁ I₁ K₁)
  → FunctorCompose L₁₁ M₁₁ N₁₁
  → FunctorCompose L₂₁ M₂₁ N₂₁
  → Dependent₁FunctorCompose L₂₂ M₂₂ N₂₂
  → FunctorCompose
    (functor-sigma-sum L₂₂ s₁)
    (functor-sigma-sum M₂₂ t₁)
    (functor-sigma-sum N₂₂ u₁)
functor-compose-sigma-sum
  {L₂₂ = L₂₂} {M₂₂ = M₂₂} {N₂₂ = N₂₂} s₁ t₁ u₁ p₁₁ p₂₁ p₂₂
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
    (functor-compose-sigma-maybe p₂₁ p₂₂)

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
  → {H₂₁ : Functor C₁₂₁ C₂₂₁}
  → {I₁₁ : Functor D₁₁₁ D₂₁₁}
  → {I₂₁ : Functor D₁₂₁ D₂₂₁}
  → {J₁₁₁ : Functor C₁₁₁ D₁₁₁}
  → {J₁₂₁ : Functor C₁₂₁ D₁₂₁}
  → {J₂₁₁ : Functor C₂₁₁ D₂₁₁}
  → {J₂₂₁ : Functor C₂₂₁ D₂₂₁}
  → {H₂₂ : Dependent₁Functor C₁₂₂ C₂₂₂ H₂₁}
  → {I₂₂ : Dependent₁Functor D₁₂₂ D₂₂₂ I₂₁}
  → {J₁₂₂ : Dependent₁Functor C₁₂₂ D₁₂₂ J₁₂₁}
  → {J₂₂₂ : Dependent₁Functor C₂₂₂ D₂₂₂ J₂₂₁}
  → (s₁ : SplitFunctorSquare H₁₁ H₂₁ F₁₁ F₂₁)
  → (t₁ : SplitFunctorSquare I₁₁ I₂₁ G₁₁ G₂₁)
  → (u₁₁ : SplitFunctorSquare J₁₁₁ J₁₂₁ F₁₁ G₁₁)
  → (u₂₁ : SplitFunctorSquare J₂₁₁ J₂₂₁ F₂₁ G₂₁)
  → FunctorSquare H₁₁ I₁₁ J₁₁₁ J₂₁₁
  → FunctorSquare H₂₁ I₂₁ J₁₂₁ J₂₂₁
  → Dependent₁FunctorSquare H₂₂ I₂₂ J₁₂₂ J₂₂₂
  → FunctorSquare
    (functor-sigma-sum H₂₂ s₁)
    (functor-sigma-sum I₂₂ t₁)
    (functor-sigma-sum J₁₂₂ u₁₁)
    (functor-sigma-sum J₂₂₂ u₂₁)
functor-square-sigma-sum
  {H₂₂ = H₂₂} {I₂₂ = I₂₂} {J₁₂₂ = J₁₂₂} {J₂₂₂ = J₂₂₂} s₁ t₁ u₁₁ u₂₁ v₁₁ v₂₁ v₂₂
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
    (functor-square-sigma-maybe v₂₁ v₂₂)

