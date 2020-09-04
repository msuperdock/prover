module Prover.Category.Dependent1.Split where

open import Prover.Category
  using (Category; FunctorEqual; functor-identity'; functor-square-identity-eq;
    functor-sym)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor; Dependent₁FunctorSquare)
open import Prover.Category.Dependent1.Partial
  using (Dependent₁PartialFunctor; Dependent₁PartialFunctorSquare)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare; SplitFunctorSquare')
open import Prover.Prelude

-- ## Dependent₁SplitFunctor

record Dependent₁SplitFunctor
  {C : Category}
  (C' D' : Dependent₁Category C)
  : Set
  where

  no-eta-equality

  field

    split-functor
      : (x : Category.Object C)
      → SplitFunctor
        (Dependent₁Category.category C' x)
        (Dependent₁Category.category D' x)

    split-functor-square
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → SplitFunctorSquare
        (Dependent₁Category.functor C' f)
        (Dependent₁Category.functor D' f)
        (split-functor x)
        (split-functor y)

  partial-dependent-functor
    : Dependent₁PartialFunctor C' D'
  partial-dependent-functor
    = record
    { partial-functor
      = SplitFunctor.partial-functor ∘ split-functor
    ; partial-functor-square
      = SplitFunctorSquare.partial-functor ∘ split-functor-square
    }

  open Dependent₁PartialFunctor partial-dependent-functor public

  dependent-functor
    : Dependent₁Functor D' C'
  dependent-functor
    = record
    { functor
      = functor-identity' C
    ; functor'
      = SplitFunctor.functor ∘ split-functor
    ; functor-square
      = SplitFunctorSquare.functor ∘ split-functor-square
    }

  open Dependent₁Functor dependent-functor public using () renaming
    ( base'
      to unbase
    ; map'
      to unmap
    ; base-commutative
      to unbase-commutative
    )

  base-unbase
    : (x : Category.Object C)
    → (x' : Dependent₁Category.Object D' x)
    → base x (unbase x x') ≡ just x'
  base-unbase x
    = SplitFunctor.base-unbase
      (split-functor x)

  map-unmap
    : (x : Category.Object C)
    → {x' y' : Dependent₁Category.Object D' x}
    → (f : Dependent₁Category.Arrow D' x x' y')
    → map x (base-unbase x x') (base-unbase x y') (unmap x f) ≡ f
  map-unmap x
    = SplitFunctor.map-unmap
      (split-functor x)

  normalize-arrow
    : (x : Category.Object C)
    → {x'' : Dependent₁Category.Object D' x}
    → (x' : Dependent₁Category.Object C' x)
    → base x x' ≡ just x''
    → Dependent₁Category.Arrow C' x x' (unbase x x'')
  normalize-arrow x
    = SplitFunctor.normalize-arrow
      (split-functor x)

  normalize-valid
    : (x : Category.Object C)
    → {x'' : Dependent₁Category.Object D' x}
    → (x' : Dependent₁Category.Object C' x)
    → (p : base x x' ≡ just x'')
    → map x p (base-unbase x x'') (normalize-arrow x x' p)
      ≡ Dependent₁Category.identity D' x x''
  normalize-valid x
    = SplitFunctor.normalize-valid
      (split-functor x)

-- ## Dependent₁SplitFunctorSquare

record Dependent₁SplitFunctorSquare
  {C₁ C₂ : Category}
  {C₁' D₁' : Dependent₁Category C₁}
  {C₂' D₂' : Dependent₁Category C₂}
  (F : Dependent₁Functor C₁' C₂')
  (G : Dependent₁Functor D₁' D₂')
  (H₁ : Dependent₁SplitFunctor C₁' D₁')
  (H₂ : Dependent₁SplitFunctor C₂' D₂')
  : Set
  where

  field

    functor
      : FunctorEqual
        (Dependent₁Functor.functor F)
        (Dependent₁Functor.functor G)

  field

    split-functor
      : (x₁ : Category.Object C₁)
      → SplitFunctorSquare'
        (Dependent₁Functor.functor' F x₁)
        (Dependent₁Functor.functor' G x₁)
        (Dependent₁SplitFunctor.split-functor H₁ x₁)
        (Dependent₁SplitFunctor.split-functor H₂ (Dependent₁Functor.base F x₁))

  partial-dependent-functor
    : Dependent₁PartialFunctorSquare F G
      (Dependent₁SplitFunctor.partial-dependent-functor H₁)
      (Dependent₁SplitFunctor.partial-dependent-functor H₂)
  partial-dependent-functor
    = record
    { functor
      = functor
    ; partial-functor
      = λ x₁ → SplitFunctorSquare'.partial-functor
        (split-functor x₁)
    }

  dependent-functor
    : Dependent₁FunctorSquare G F
      (Dependent₁SplitFunctor.dependent-functor H₁)
      (Dependent₁SplitFunctor.dependent-functor H₂)
  dependent-functor
    = record
    { functor
      = functor-square-identity-eq (functor-sym functor)
    ; functor'
      = λ x₁ → SplitFunctorSquare'.functor
        (Dependent₁Category.category C₂')
        (Dependent₁Category.category D₂')
        (Dependent₁SplitFunctor.split-functor H₂)
        (FunctorEqual.base functor x₁)
        (split-functor x₁)
    }

