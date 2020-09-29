module Prover.Category.Dependent1.Split where

open import Prover.Category
  using (Category; Functor; functor-identity')
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor; Dependent₁FunctorSquare)
open import Prover.Category.Dependent1.Partial
  using (Dependent₁PartialFunctor; Dependent₁PartialFunctorSquare)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)

-- ## Dependent₁SplitFunctor

Dependent₁SplitFunctor
  : {C : Category}
  → Dependent₁Category C
  → Dependent₁Category C
  → Set
Dependent₁SplitFunctor
  = DependentSplitFunctor

module Dependent₁SplitFunctor
  {C : Category}
  {C' D' : Dependent₁Category C}
  (F : Dependent₁SplitFunctor C' D')
  where

  open DependentSplitFunctor F public

  open module SplitFunctor' x
    = SplitFunctor (split-functor x)
    public
  
  open module SplitFunctorSquare' {x = x} {y = y} f
    = SplitFunctorSquare (split-functor-square {x = x} {y = y} f)
    public using () renaming
    ( partial-functor
      to partial-functor-square
    ; base
      to base-square
    ; functor
      to functor-square
    ; unbase
      to unbase-square
    )

  dependent₁-partial-functor
    : Dependent₁PartialFunctor C' D'
  dependent₁-partial-functor
    = record
    { partial-functor
      = partial-functor
    ; partial-functor-square
      = partial-functor-square
    }

  dependent₁-functor
    : Dependent₁Functor D' C' (functor-identity' C)
  dependent₁-functor
    = record
    { functor
      = functor
    ; functor-square
      = functor-square
    }

-- ## Dependent₁SplitFunctorSquare

Dependent₁SplitFunctorSquare
  : {C₁ C₂ : Category}
  → {C₁' D₁' : Dependent₁Category C₁}
  → {C₂' D₂' : Dependent₁Category C₂}
  → {F : Functor C₁ C₂}
  → Dependent₁Functor C₁' C₂' F
  → Dependent₁Functor D₁' D₂' F
  → Dependent₁SplitFunctor C₁' D₁'
  → Dependent₁SplitFunctor C₂' D₂'
  → Set
Dependent₁SplitFunctorSquare
  = DependentSplitFunctorSquare

module Dependent₁SplitFunctorSquare
  {C₁ C₂ : Category}
  {C₁' D₁' : Dependent₁Category C₁}
  {C₂' D₂' : Dependent₁Category C₂}
  {F : Functor C₁ C₂}
  {F' : Dependent₁Functor C₁' C₂' F}
  {G' : Dependent₁Functor D₁' D₂' F}
  {H₁ : Dependent₁SplitFunctor C₁' D₁'}
  {H₂ : Dependent₁SplitFunctor C₂' D₂'}
  (s : Dependent₁SplitFunctorSquare F' G' H₁ H₂)
  where

  open DependentSplitFunctorSquare s public

  open module SplitFunctor' x₁
    = SplitFunctorSquare (split-functor x₁)
    public

  dependent₁-partial-functor
    : Dependent₁PartialFunctorSquare F' G'
      (Dependent₁SplitFunctor.dependent₁-partial-functor H₁)
      (Dependent₁SplitFunctor.dependent₁-partial-functor H₂)
  dependent₁-partial-functor
    = record
    { partial-functor
      = partial-functor
    }

  dependent₁-functor
    : Dependent₁FunctorSquare G' F'
      (Dependent₁SplitFunctor.dependent₁-functor H₁)
      (Dependent₁SplitFunctor.dependent₁-functor H₂)
  dependent₁-functor
    = record
    { functor
      = functor
    }

