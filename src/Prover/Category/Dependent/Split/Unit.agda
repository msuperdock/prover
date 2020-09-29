module Prover.Category.Dependent.Split.Unit where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; DependentSimpleFunctor)
open import Prover.Category.Dependent.Simple.Split
  using (DependentSimpleSplitFunctor; DependentSimpleSplitFunctorSquare)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare)
open import Prover.Category.Dependent.Unit
  using (dependent-category-unit; dependent-functor-unit)
open import Prover.Category.Split.Unit
  using (split-functor-unit; split-functor-square-unit)
open import Prover.Prelude

-- ## Types

-- ### DependentSplitFunctor

dependent-split-functor-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentSimpleCategory C}
  → DependentSimpleSplitFunctor C' D'
  → DependentSplitFunctor
    (dependent-category-unit C')
    (dependent-category-unit D')

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-unit
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' D₁' : DependentSimpleCategory C₁}
  → {C₂' D₂' : DependentSimpleCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → {F' : DependentSimpleFunctor C₁' C₂' F}
  → {G' : DependentSimpleFunctor D₁' D₂' F}
  → {H₁ : DependentSimpleSplitFunctor C₁' D₁'}
  → {H₂ : DependentSimpleSplitFunctor C₂' D₂'}
  → DependentSimpleSplitFunctorSquare F' G' H₁ H₂
  → DependentSplitFunctorSquare
    (dependent-functor-unit F')
    (dependent-functor-unit G')
    (dependent-split-functor-unit H₁)
    (dependent-split-functor-unit H₂)

-- ## Definitions

-- ### DependentSplitFunctor

dependent-split-functor-unit {n = zero} F
  = split-functor-unit F

dependent-split-functor-unit {n = suc _} F
  = record
  { split-functor
    = λ x → dependent-split-functor-unit
      (DependentSimpleSplitFunctor.split-functor F x)
  ; split-functor-square
    = λ f → dependent-split-functor-square-unit
      (DependentSimpleSplitFunctor.split-functor-square F f)
  }

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-unit {n = zero} s
  = split-functor-square-unit s

dependent-split-functor-square-unit {n = suc _} s
  = record
  { split-functor
    = λ x₁ → dependent-split-functor-square-unit
      (DependentSimpleSplitFunctorSquare.split-functor s x₁)
  }

