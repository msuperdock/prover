module Prover.Category.Dependent.Simple.Split.Convert where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor)
open import Prover.Category.Dependent.Simple.Convert
  using (dependent-category-simple; dependent-functor-simple)
open import Prover.Category.Dependent.Simple.Split
  using (DependentSimpleSplitFunctor; DependentSimpleSplitFunctorSquare)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Prelude

-- ## Types

-- ### DependentSplitFunctor

dependent-split-functor-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → DependentSplitFunctor C' D'
  → DependentSimpleSplitFunctor
    (dependent-category-simple C')
    (dependent-category-simple D')

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-simple
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' D₁' : DependentCategory C₁}
  → {C₂' D₂' : DependentCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' D₂' F}
  → {H₁ : DependentSplitFunctor C₁' D₁'}
  → {H₂ : DependentSplitFunctor C₂' D₂'}
  → DependentSplitFunctorSquare F' G' H₁ H₂
  → DependentSimpleSplitFunctorSquare
    (dependent-functor-simple F')
    (dependent-functor-simple G')
    (dependent-split-functor-simple H₁)
    (dependent-split-functor-simple H₂)

-- ## Definitions

-- ### DependentSplitFunctor

dependent-split-functor-simple {n = zero} F
  = SplitFunctor.split-function F

dependent-split-functor-simple {n = suc _} F
  = record
  { split-functor
    = λ x → dependent-split-functor-simple
      (DependentSplitFunctor.split-functor F x)
  ; split-functor-square
    = λ f → dependent-split-functor-square-simple
      (DependentSplitFunctor.split-functor-square F f)
  }

-- ### DependentSplitFunctorSquare

dependent-split-functor-square-simple {n = zero} s
  = SplitFunctorSquare.split-function s

dependent-split-functor-square-simple {n = suc _} s
  = record
  { split-functor
    = λ x₁ → dependent-split-functor-square-simple
      (DependentSplitFunctorSquare.split-functor s x₁)
  }

