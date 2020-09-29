module Prover.Category.Dependent.Split where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor)
open import Prover.Category.Dependent.Bool
  using (DependentBoolFunction)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare; split-functor-compose;
    split-functor-square-compose)
open import Prover.Prelude

-- ## Types

-- ### DependentSplitFunctor

DependentSplitFunctor
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → DependentCategory C
  → Set

record DependentSplitFunctor'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' D' : DependentCategory C)
  : Set

-- ### DependentSplitFunctorSquare

DependentSplitFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' D₁' : DependentCategory C₁}
  → {C₂' D₂' : DependentCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → DependentFunctor C₁' C₂' F
  → DependentFunctor D₁' D₂' F
  → DependentSplitFunctor C₁' D₁'
  → DependentSplitFunctor C₂' D₂'
  → Set
  
record DependentSplitFunctorSquare'
  {n : ℕ}
  {C₁ C₂ : ChainCategory (suc n)}
  {C₁' D₁' : DependentCategory C₁}
  {C₂' D₂' : DependentCategory C₂}
  {F : ChainFunctor C₁ C₂}
  (F' : DependentFunctor C₁' C₂' F)
  (G' : DependentFunctor D₁' D₂' F)
  (H₁ : DependentSplitFunctor C₁' D₁')
  (H₂ : DependentSplitFunctor C₂' D₂')
  : Set

-- ## Definitions

-- ### DependentSplitFunctor

DependentSplitFunctor {n = zero}
  = SplitFunctor
DependentSplitFunctor {n = suc _}
  = DependentSplitFunctor'

record DependentSplitFunctor' {_ C} C' D' where

  inductive

  no-eta-equality

  field

    split-functor
      : (x : ChainCategory.Object C)
      → DependentSplitFunctor
        (DependentCategory.category C' x)
        (DependentCategory.category D' x)

    split-functor-square
      : {x y : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C x y)
      → DependentSplitFunctorSquare
        (DependentCategory.functor C' f)
        (DependentCategory.functor D' f)
        (split-functor x)
        (split-functor y)

module DependentSplitFunctor
  = DependentSplitFunctor'

-- ### DependentSplitFunctorSquare

DependentSplitFunctorSquare {n = zero}
  = SplitFunctorSquare
DependentSplitFunctorSquare {n = suc _}
  = DependentSplitFunctorSquare'

record DependentSplitFunctorSquare' {_ C₁ _ _ _ _ _ F} F' G' H₁ H₂ where

  inductive

  field

    split-functor
      : (x₁ : ChainCategory.Object C₁)
      → DependentSplitFunctorSquare
        (DependentFunctor.functor F' x₁)
        (DependentFunctor.functor G' x₁)
        (DependentSplitFunctor.split-functor H₁ x₁)
        (DependentSplitFunctor.split-functor H₂ (ChainFunctor.base F x₁))

module DependentSplitFunctorSquare
  = DependentSplitFunctorSquare'

-- ## Conversion

dependent-split-functor-bool
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → DependentSplitFunctor C' D'
  → DependentBoolFunction C'

dependent-split-functor-bool {n = zero} F
  = SplitFunctor.bool-function F

dependent-split-functor-bool {n = suc _} F
  = record
  { function
    = λ x → dependent-split-functor-bool
      (DependentSplitFunctor.split-functor F x)
  }

-- ## Compose

dependent-split-functor-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' E' : DependentCategory C}
  → DependentSplitFunctor D' E'
  → DependentSplitFunctor C' D'
  → DependentSplitFunctor C' E'

dependent-split-functor-square-compose
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' D₁' E₁' : DependentCategory C₁}
  → {C₂' D₂' E₂' : DependentCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' D₂' F}
  → {H' : DependentFunctor E₁' E₂' F}
  → {I₁ : DependentSplitFunctor D₁' E₁'}
  → {I₂ : DependentSplitFunctor D₂' E₂'}
  → {J₁ : DependentSplitFunctor C₁' D₁'}
  → {J₂ : DependentSplitFunctor C₂' D₂'}
  → DependentSplitFunctorSquare G' H' I₁ I₂
  → DependentSplitFunctorSquare F' G' J₁ J₂
  → DependentSplitFunctorSquare F' H'
    (dependent-split-functor-compose I₁ J₁)
    (dependent-split-functor-compose I₂ J₂)

dependent-split-functor-compose {n = zero} F G
  = split-functor-compose F G

dependent-split-functor-compose {n = suc _} F G
  = record
  { split-functor
    = λ x → dependent-split-functor-compose
      (DependentSplitFunctor.split-functor F x)
      (DependentSplitFunctor.split-functor G x)
  ; split-functor-square
    = λ f → dependent-split-functor-square-compose
      (DependentSplitFunctor.split-functor-square F f)
      (DependentSplitFunctor.split-functor-square G f)
  }

dependent-split-functor-square-compose {n = zero} s t
  = split-functor-square-compose s t

dependent-split-functor-square-compose {n = suc _} s t
  = record
  { split-functor
    = λ x₁ → dependent-split-functor-square-compose
      (DependentSplitFunctorSquare.split-functor s x₁)
      (DependentSplitFunctorSquare.split-functor t x₁)
  }

