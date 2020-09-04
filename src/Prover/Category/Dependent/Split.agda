module Prover.Category.Dependent.Split where

open import Prover.Category
  using (FunctorEqual; functor-refl)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; dependent-category₀;
    dependent-category₁; dependent-functor₀; dependent-functor₁)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Dependent1.Split
  using (Dependent₁SplitFunctor; Dependent₁SplitFunctorSquare)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare; SplitFunctorSquare';
    split-functor-compose; split-functor-square'; split-functor-square-compose)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types
  
  -- #### DependentSplitFunctor
  
  data DependentSplitFunctor
    : {n : ℕ}
    → {C : ChainCategory n}
    → DependentCategory C
    → DependentCategory C
    → Set
  
  -- #### DependentSplitFunctorSquare
  
  data DependentSplitFunctorSquare
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
  
  -- ### Interface
 
  -- #### DependentSplitFunctor

  dependent-split-functor₀
    : {C : ChainCategory zero}
    → {C' D' : DependentCategory C}
    → DependentSplitFunctor C' D'
    → SplitFunctor
      (dependent-category₀ C')
      (dependent-category₀ D')
  
  dependent-split-functor-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : DependentCategory C}
    → DependentSplitFunctor C' D'
    → (x : ChainCategory.Object C)
    → DependentSplitFunctor
      (DependentCategory.tail C' x)
      (DependentCategory.tail D' x)

  dependent-split-functor-dependent-split-functor-square
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : DependentCategory C}
    → (F : DependentSplitFunctor C' D')
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → DependentSplitFunctorSquare
      (DependentCategory.dependent-functor C' f)
      (DependentCategory.dependent-functor D' f)
      (dependent-split-functor-tail F x)
      (dependent-split-functor-tail F y)

  -- #### DependentSplitFunctorSquare

  dependent-split-functor-square₀
    : {C₁ C₂ : ChainCategory zero}
    → {C₁' D₁' : DependentCategory C₁}
    → {C₂' D₂' : DependentCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → {F' : DependentFunctor C₁' C₂' F}
    → {G' : DependentFunctor D₁' D₂' F}
    → {H₁ : DependentSplitFunctor C₁' D₁'}
    → {H₂ : DependentSplitFunctor C₂' D₂'}
    → DependentSplitFunctorSquare F' G' H₁ H₂
    → SplitFunctorSquare
      (dependent-functor₀ F')
      (dependent-functor₀ G')
      (dependent-split-functor₀ H₁)
      (dependent-split-functor₀ H₂)

  dependent-split-functor-square-tail
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory (suc n)}
    → {C₁' D₁' : DependentCategory C₁}
    → {C₂' D₂' : DependentCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → {F' : DependentFunctor C₁' C₂' F}
    → {G' : DependentFunctor D₁' D₂' F}
    → {H₁ : DependentSplitFunctor C₁' D₁'}
    → {H₂ : DependentSplitFunctor C₂' D₂'}
    → DependentSplitFunctorSquare F' G' H₁ H₂
    → (x₁ : ChainCategory.Object C₁)
    → DependentSplitFunctorSquare
      (DependentFunctor.tail F' x₁)
      (DependentFunctor.tail G' x₁)
      (dependent-split-functor-tail H₁ x₁)
      (dependent-split-functor-tail H₂ (ChainFunctor.base F x₁))

  -- ### Definitions
  
  -- #### DependentSplitFunctor
  
  data DependentSplitFunctor where
    
    nil
      : {C : ChainCategory zero}
      → {C' D' : DependentCategory C}
      → SplitFunctor
        (dependent-category₀ C')
        (dependent-category₀ D')
      → DependentSplitFunctor C' D'

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' D' : DependentCategory C}
      → (F : (x : ChainCategory.Object C)
        → DependentSplitFunctor
          (DependentCategory.tail C' x)
          (DependentCategory.tail D' x))
      → ({x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → DependentSplitFunctorSquare
          (DependentCategory.dependent-functor C' f)
          (DependentCategory.dependent-functor D' f)
          (F x)
          (F y))
      → DependentSplitFunctor C' D'
  
  dependent-split-functor₀ (nil F)
    = F

  dependent-split-functor-tail (cons F _)
    = F

  dependent-split-functor-dependent-split-functor-square (cons _ s)
    = s

  -- #### DependentSplitFunctorSquare
  
  data DependentSplitFunctorSquare where
  
    nil
      : {C₁ C₂ : ChainCategory zero}
      → {C₁' D₁' : DependentCategory C₁}
      → {C₂' D₂' : DependentCategory C₂}
      → {F : ChainFunctor C₁ C₂}
      → {F' : DependentFunctor C₁' C₂' F}
      → {G' : DependentFunctor D₁' D₂' F}
      → {H₁ : DependentSplitFunctor C₁' D₁'}
      → {H₂ : DependentSplitFunctor C₂' D₂'}
      → SplitFunctorSquare
        (dependent-functor₀ F')
        (dependent-functor₀ G')
        (dependent-split-functor₀ H₁)
        (dependent-split-functor₀ H₂)
      → DependentSplitFunctorSquare F' G' H₁ H₂

    cons
      : {n : ℕ}
      → {C₁ C₂ : ChainCategory (suc n)}
      → {C₁' D₁' : DependentCategory C₁}
      → {C₂' D₂' : DependentCategory C₂}
      → {F : ChainFunctor C₁ C₂}
      → {F' : DependentFunctor C₁' C₂' F}
      → {G' : DependentFunctor D₁' D₂' F}
      → {H₁ : DependentSplitFunctor C₁' D₁'}
      → {H₂ : DependentSplitFunctor C₂' D₂'}
      → ((x₁ : ChainCategory.Object C₁)
        → DependentSplitFunctorSquare
          (DependentFunctor.tail F' x₁)
          (DependentFunctor.tail G' x₁)
          (dependent-split-functor-tail H₁ x₁)
          (dependent-split-functor-tail H₂ (ChainFunctor.base F x₁)))
      → DependentSplitFunctorSquare F' G' H₁ H₂

  dependent-split-functor-square₀ (nil s)
    = s

  dependent-split-functor-square-tail (cons s)
    = s

  -- ### Destruction

  -- #### DependentSplitFunctor

  module _
    {C : ChainCategory (suc zero)}
    {C' D' : DependentCategory C}
    where

    module DependentSplitFunctor₁
      (F : DependentSplitFunctor C' D')
      where

      split-functor
        : (x : ChainCategory.Object C)
        → SplitFunctor
          (Dependent₁Category.category
            (dependent-category₁ C') x)
          (Dependent₁Category.category
            (dependent-category₁ D') x)
      split-functor x
        = dependent-split-functor₀
          (dependent-split-functor-tail F x)

      abstract

        split-functor-square
          : {x y : ChainCategory.Object C}
          → (f : ChainCategory.Arrow C x y)
          → SplitFunctorSquare
            (Dependent₁Category.functor
              (dependent-category₁ C') f)
            (Dependent₁Category.functor
              (dependent-category₁ D') f)
            (split-functor x)
            (split-functor y)
        split-functor-square f
          = dependent-split-functor-square₀
            (dependent-split-functor-dependent-split-functor-square F f)

    dependent-split-functor₁
      : DependentSplitFunctor C' D'
      → Dependent₁SplitFunctor
        (dependent-category₁ C')
        (dependent-category₁ D')
    dependent-split-functor₁ F
      = record {DependentSplitFunctor₁ F}

  -- #### DependentSplitFunctorSquare

  module _
    {C₁ C₂ : ChainCategory (suc zero)}
    {C₁' D₁' : DependentCategory C₁}
    {C₂' D₂' : DependentCategory C₂}
    {F : ChainFunctor C₁ C₂}
    {F' : DependentFunctor C₁' C₂' F}
    {G' : DependentFunctor D₁' D₂' F}
    {H₁ : DependentSplitFunctor C₁' D₁'}
    {H₂ : DependentSplitFunctor C₂' D₂'}
    where

    module DependentSplitFunctorSquare₁
      (s : DependentSplitFunctorSquare F' G' H₁ H₂)
      where

      functor
        : FunctorEqual
          (Dependent₁Functor.functor
            (dependent-functor₁ F'))
          (Dependent₁Functor.functor
            (dependent-functor₁ G'))
      functor
        = functor-refl

      split-functor
        : (x₁ : ChainCategory.Object C₁)
        → SplitFunctorSquare'
          (Dependent₁Functor.functor'
            (dependent-functor₁ F') x₁)
          (Dependent₁Functor.functor'
            (dependent-functor₁ G') x₁)
          (Dependent₁SplitFunctor.split-functor
            (dependent-split-functor₁ H₁) x₁)
          (Dependent₁SplitFunctor.split-functor
            (dependent-split-functor₁ H₂)
            (Dependent₁Functor.base (dependent-functor₁ F') x₁))
      split-functor x₁
        = split-functor-square'
        $ dependent-split-functor-square₀
          (dependent-split-functor-square-tail s x₁)

    dependent-split-functor-square₁
      : DependentSplitFunctorSquare F' G' H₁ H₂
      → Dependent₁SplitFunctorSquare
        (dependent-functor₁ F')
        (dependent-functor₁ G')
        (dependent-split-functor₁ H₁)
        (dependent-split-functor₁ H₂)
    dependent-split-functor-square₁ s
      = record {DependentSplitFunctorSquare₁ s}

  -- ### Compose

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

  dependent-split-functor-compose
    {n = zero} F G
    = nil
      (split-functor-compose
        (dependent-split-functor₀ F)
        (dependent-split-functor₀ G))
  dependent-split-functor-compose
    {n = suc _} F G
    = cons
      (λ x → dependent-split-functor-compose
        (dependent-split-functor-tail F x)
        (dependent-split-functor-tail G x))
      (λ f → dependent-split-functor-square-compose
        (dependent-split-functor-dependent-split-functor-square F f)
        (dependent-split-functor-dependent-split-functor-square G f))

  dependent-split-functor-square-compose
    {n = zero} s t
    = nil
      (split-functor-square-compose
        (dependent-split-functor-square₀ s)
        (dependent-split-functor-square₀ t))
  dependent-split-functor-square-compose
    {n = suc _} s t
    = cons
      (λ x₁ → dependent-split-functor-square-compose
        (dependent-split-functor-square-tail s x₁)
        (dependent-split-functor-square-tail t x₁))

-- ## Modules

-- ### DependentSplitFunctor

DependentSplitFunctor
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → DependentCategory C
  → Set
DependentSplitFunctor
  = Internal.DependentSplitFunctor
  
open Internal.DependentSplitFunctor public

open Internal public
  using (dependent-split-functor₀; dependent-split-functor₁;
    dependent-split-functor-compose)

module DependentSplitFunctor where

  open Internal public using () renaming
    ( dependent-split-functor-dependent-split-functor-square
      to dependent-split-functor-square
    ; dependent-split-functor-tail
      to tail
    )

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
DependentSplitFunctorSquare
  = Internal.DependentSplitFunctorSquare
  
open Internal.DependentSplitFunctorSquare public

open Internal public
  using (dependent-split-functor-square₀; dependent-split-functor-square₁)

module DependentSplitFunctorSquare where

  open Internal public using () renaming
    ( dependent-split-functor-square-tail
      to tail
    )

