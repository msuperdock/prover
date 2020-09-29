module Prover.Function.Split.Compose where

open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare; split-functor-compose;
    split-functor-square-compose)
open import Prover.Category.Split.Unit
  using (split-functor-unit; split-functor-square-unit)
open import Prover.Function
  using (Function)
open import Prover.Function.Split
  using (SplitFunction; SplitFunctionSquare)
open import Prover.Prelude

-- ## SplitFunction

split-function-compose
  : {A B C : Set}
  → SplitFunction B C
  → SplitFunction A B
  → SplitFunction A C
split-function-compose F G
  = SplitFunctor.split-function
  $ split-functor-compose
    (split-functor-unit F)
    (split-functor-unit G)

-- ## SplitFunctionSquare

split-function-square-compose
  : {A₁ A₂ B₁ B₂ C₁ C₂ : Set}
  → {F : Function A₁ A₂}
  → {G : Function B₁ B₂}
  → {H : Function C₁ C₂}
  → {I₁ : SplitFunction B₁ C₁}
  → {I₂ : SplitFunction B₂ C₂}
  → {J₁ : SplitFunction A₁ B₁}
  → {J₂ : SplitFunction A₂ B₂}
  → SplitFunctionSquare G H I₁ I₂
  → SplitFunctionSquare F G J₁ J₂
  → SplitFunctionSquare F H
    (split-function-compose I₁ J₁)
    (split-function-compose I₂ J₂)
split-function-square-compose s t
  = SplitFunctorSquare.split-function
  $ split-functor-square-compose
    (split-functor-square-unit s)
    (split-functor-square-unit t)

