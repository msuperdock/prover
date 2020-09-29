module Prover.Category.Dependent.Simple.Split where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; DependentSimpleFunctor;
    dependent-simple-category-set)
open import Prover.Category.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Category.Dependent.Simple.Partial
  using (DependentSimplePartialFunction; dependent-simple-partial-function-bool)
open import Prover.Function.Split
  using (SplitFunction; SplitFunctionSquare)
open import Prover.Function.Split.Compose
  using (split-function-compose; split-function-square-compose)
open import Prover.Prelude

-- ## Types

-- ### DependentSimpleSplitFunctor

DependentSimpleSplitFunctor
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentSimpleCategory C
  → Set

record DependentSimpleSplitFunctor'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' D' : DependentSimpleCategory C)
  : Set

-- ### DependentSimpleSplitFunctorSquare

DependentSimpleSplitFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' D₁' : DependentSimpleCategory C₁}
  → {C₂' D₂' : DependentSimpleCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → DependentSimpleFunctor C₁' C₂' F
  → DependentSimpleFunctor D₁' D₂' F
  → DependentSimpleSplitFunctor C₁' D₁'
  → DependentSimpleSplitFunctor C₂' D₂'
  → Set

record DependentSimpleSplitFunctorSquare'
  {n : ℕ}
  {C₁ C₂ : ChainCategory (suc n)}
  {C₁' D₁' : DependentSimpleCategory C₁}
  {C₂' D₂' : DependentSimpleCategory C₂}
  {F : ChainFunctor C₁ C₂}
  (F' : DependentSimpleFunctor C₁' C₂' F)
  (G' : DependentSimpleFunctor D₁' D₂' F)
  (H₁ : DependentSimpleSplitFunctor C₁' D₁')
  (H₂ : DependentSimpleSplitFunctor C₂' D₂')
  : Set

-- ## Definitions

-- ### DependentSimpleSplitFunctor

DependentSimpleSplitFunctor {n = zero}
  = SplitFunction
DependentSimpleSplitFunctor {n = suc _}
  = DependentSimpleSplitFunctor'

record DependentSimpleSplitFunctor' {_ C} C' D' where

  inductive

  no-eta-equality

  field

    split-functor
      : (x : ChainCategory.Object C)
      → DependentSimpleSplitFunctor
        (DependentSimpleCategory.category C' x)
        (DependentSimpleCategory.category D' x)

    split-functor-square
      : {x y : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C x y)
      → DependentSimpleSplitFunctorSquare
        (DependentSimpleCategory.functor C' f)
        (DependentSimpleCategory.functor D' f)
        (split-functor x)
        (split-functor y)

module DependentSimpleSplitFunctor
  = DependentSimpleSplitFunctor'

-- ### DependentSimpleSplitFunctorSquare

DependentSimpleSplitFunctorSquare {n = zero}
  = SplitFunctionSquare
DependentSimpleSplitFunctorSquare {n = suc _}
  = DependentSimpleSplitFunctorSquare'

record DependentSimpleSplitFunctorSquare' {_ C₁ _ _ _ _ _ F} F' G' H₁ H₂ where

  inductive

  field

    split-functor
      : (x₁ : ChainCategory.Object C₁)
      → DependentSimpleSplitFunctorSquare
        (DependentSimpleFunctor.functor F' x₁)
        (DependentSimpleFunctor.functor G' x₁)
        (DependentSimpleSplitFunctor.split-functor H₁ x₁)
        (DependentSimpleSplitFunctor.split-functor H₂
          (ChainFunctor.base F x₁))

module DependentSimpleSplitFunctorSquare
  = DependentSimpleSplitFunctorSquare'

-- ## Conversion

dependent-simple-split-functor-partial
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C' D'
  → DependentSimplePartialFunction C'
    (dependent-simple-category-set D')

dependent-simple-split-functor-partial {n = zero} F
  = SplitFunction.partial-function F

dependent-simple-split-functor-partial {n = suc _} F
  = record
  { partial-function
    = λ x → dependent-simple-split-functor-partial
      (DependentSimpleSplitFunctor.split-functor F x)
  }

dependent-simple-split-functor-bool
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C' D'
  → DependentSimpleBoolFunction C'
dependent-simple-split-functor-bool
  = dependent-simple-partial-function-bool
  ∘ dependent-simple-split-functor-partial

-- ## Compose

dependent-simple-split-functor-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' E' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor D' E'
  → DependentSimpleSplitFunctor C' D'
  → DependentSimpleSplitFunctor C' E'

dependent-simple-split-functor-square-compose
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' D₁' E₁' : DependentSimpleCategory C₁}
  → {C₂' D₂' E₂' : DependentSimpleCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → {F' : DependentSimpleFunctor C₁' C₂' F}
  → {G' : DependentSimpleFunctor D₁' D₂' F}
  → {H' : DependentSimpleFunctor E₁' E₂' F}
  → {I₁ : DependentSimpleSplitFunctor D₁' E₁'}
  → {I₂ : DependentSimpleSplitFunctor D₂' E₂'}
  → {J₁ : DependentSimpleSplitFunctor C₁' D₁'}
  → {J₂ : DependentSimpleSplitFunctor C₂' D₂'}
  → DependentSimpleSplitFunctorSquare G' H' I₁ I₂
  → DependentSimpleSplitFunctorSquare F' G' J₁ J₂
  → DependentSimpleSplitFunctorSquare F' H'
    (dependent-simple-split-functor-compose I₁ J₁)
    (dependent-simple-split-functor-compose I₂ J₂)

dependent-simple-split-functor-compose {n = zero} F G
  = split-function-compose F G

dependent-simple-split-functor-compose {n = suc _} F G
  = record
  { split-functor
    = λ x → dependent-simple-split-functor-compose
      (DependentSimpleSplitFunctor.split-functor F x)
      (DependentSimpleSplitFunctor.split-functor G x)
  ; split-functor-square
    = λ f → dependent-simple-split-functor-square-compose
      (DependentSimpleSplitFunctor.split-functor-square F f)
      (DependentSimpleSplitFunctor.split-functor-square G f)
  }

dependent-simple-split-functor-square-compose {n = zero} s t
  = split-function-square-compose s t

dependent-simple-split-functor-square-compose {n = suc _} s t
  = record
  { split-functor
    = λ x₁ → dependent-simple-split-functor-square-compose
      (DependentSimpleSplitFunctorSquare.split-functor s x₁)
      (DependentSimpleSplitFunctorSquare.split-functor t x₁)
  }

