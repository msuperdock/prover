module Prover.Category.Indexed.Split where

open import Prover.Category
  using (DependentCategory; DependentFunctor; FunctorEqual; functor-refl)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor; indexed-category₀; indexed-category₁;
    indexed-functor₀; indexed-functor₁)
open import Prover.Category.Split
  using (SplitDependentFunctor; SplitDependentFunctorSquare; SplitFunctor;
    SplitFunctorSquare; SplitFunctorSquare'; split-functor-compose;
    split-functor-square'; split-functor-square-compose)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types
  
  -- #### IndexedSplitFunctor
  
  data IndexedSplitFunctor
    : {n : ℕ}
    → {C : ChainCategory n}
    → IndexedCategory C
    → IndexedCategory C
    → Set
  
  -- #### IndexedSplitFunctorSquare
  
  data IndexedSplitFunctorSquare
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory n}
    → {C₁' D₁' : IndexedCategory C₁}
    → {C₂' D₂' : IndexedCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → IndexedFunctor C₁' C₂' F
    → IndexedFunctor D₁' D₂' F
    → IndexedSplitFunctor C₁' D₁'
    → IndexedSplitFunctor C₂' D₂'
    → Set
  
  -- ### Interface
 
  -- #### IndexedSplitFunctor

  indexed-split-functor₀
    : {C : ChainCategory zero}
    → {C' D' : IndexedCategory C}
    → IndexedSplitFunctor C' D'
    → SplitFunctor
      (indexed-category₀ C')
      (indexed-category₀ D')
  
  indexed-split-functor-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : IndexedCategory C}
    → IndexedSplitFunctor C' D'
    → (x : ChainCategory.Object C)
    → IndexedSplitFunctor
      (IndexedCategory.tail C' x)
      (IndexedCategory.tail D' x)

  indexed-split-functor-indexed-split-functor-square
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : IndexedCategory C}
    → (F : IndexedSplitFunctor C' D')
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → IndexedSplitFunctorSquare
      (IndexedCategory.indexed-functor C' f)
      (IndexedCategory.indexed-functor D' f)
      (indexed-split-functor-tail F x)
      (indexed-split-functor-tail F y)

  -- #### IndexedSplitFunctorSquare

  indexed-split-functor-square₀
    : {C₁ C₂ : ChainCategory zero}
    → {C₁' D₁' : IndexedCategory C₁}
    → {C₂' D₂' : IndexedCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → {F' : IndexedFunctor C₁' C₂' F}
    → {G' : IndexedFunctor D₁' D₂' F}
    → {H₁ : IndexedSplitFunctor C₁' D₁'}
    → {H₂ : IndexedSplitFunctor C₂' D₂'}
    → IndexedSplitFunctorSquare F' G' H₁ H₂
    → SplitFunctorSquare
      (indexed-functor₀ F')
      (indexed-functor₀ G')
      (indexed-split-functor₀ H₁)
      (indexed-split-functor₀ H₂)

  indexed-split-functor-square-tail
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory (suc n)}
    → {C₁' D₁' : IndexedCategory C₁}
    → {C₂' D₂' : IndexedCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → {F' : IndexedFunctor C₁' C₂' F}
    → {G' : IndexedFunctor D₁' D₂' F}
    → {H₁ : IndexedSplitFunctor C₁' D₁'}
    → {H₂ : IndexedSplitFunctor C₂' D₂'}
    → IndexedSplitFunctorSquare F' G' H₁ H₂
    → (x₁ : ChainCategory.Object C₁)
    → IndexedSplitFunctorSquare
      (IndexedFunctor.tail F' x₁)
      (IndexedFunctor.tail G' x₁)
      (indexed-split-functor-tail H₁ x₁)
      (indexed-split-functor-tail H₂ (ChainFunctor.base F x₁))

  -- ### Definitions
  
  -- #### IndexedSplitFunctor
  
  data IndexedSplitFunctor where
    
    nil
      : {C : ChainCategory zero}
      → {C' D' : IndexedCategory C}
      → SplitFunctor
        (indexed-category₀ C')
        (indexed-category₀ D')
      → IndexedSplitFunctor C' D'

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' D' : IndexedCategory C}
      → (F : (x : ChainCategory.Object C)
        → IndexedSplitFunctor
          (IndexedCategory.tail C' x)
          (IndexedCategory.tail D' x))
      → ({x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → IndexedSplitFunctorSquare
          (IndexedCategory.indexed-functor C' f)
          (IndexedCategory.indexed-functor D' f)
          (F x)
          (F y))
      → IndexedSplitFunctor C' D'
  
  indexed-split-functor₀ (nil F)
    = F

  indexed-split-functor-tail (cons F _)
    = F

  indexed-split-functor-indexed-split-functor-square (cons _ s)
    = s

  -- #### IndexedSplitFunctorSquare
  
  data IndexedSplitFunctorSquare where
  
    nil
      : {C₁ C₂ : ChainCategory zero}
      → {C₁' D₁' : IndexedCategory C₁}
      → {C₂' D₂' : IndexedCategory C₂}
      → {F : ChainFunctor C₁ C₂}
      → {F' : IndexedFunctor C₁' C₂' F}
      → {G' : IndexedFunctor D₁' D₂' F}
      → {H₁ : IndexedSplitFunctor C₁' D₁'}
      → {H₂ : IndexedSplitFunctor C₂' D₂'}
      → SplitFunctorSquare
        (indexed-functor₀ F')
        (indexed-functor₀ G')
        (indexed-split-functor₀ H₁)
        (indexed-split-functor₀ H₂)
      → IndexedSplitFunctorSquare F' G' H₁ H₂

    cons
      : {n : ℕ}
      → {C₁ C₂ : ChainCategory (suc n)}
      → {C₁' D₁' : IndexedCategory C₁}
      → {C₂' D₂' : IndexedCategory C₂}
      → {F : ChainFunctor C₁ C₂}
      → {F' : IndexedFunctor C₁' C₂' F}
      → {G' : IndexedFunctor D₁' D₂' F}
      → {H₁ : IndexedSplitFunctor C₁' D₁'}
      → {H₂ : IndexedSplitFunctor C₂' D₂'}
      → ((x₁ : ChainCategory.Object C₁)
        → IndexedSplitFunctorSquare
          (IndexedFunctor.tail F' x₁)
          (IndexedFunctor.tail G' x₁)
          (indexed-split-functor-tail H₁ x₁)
          (indexed-split-functor-tail H₂ (ChainFunctor.base F x₁)))
      → IndexedSplitFunctorSquare F' G' H₁ H₂

  indexed-split-functor-square₀ (nil s)
    = s

  indexed-split-functor-square-tail (cons s)
    = s

  -- ### Destruction

  -- #### IndexedSplitFunctor

  module _
    {C : ChainCategory (suc zero)}
    {C' D' : IndexedCategory C}
    where

    module IndexedSplitFunctor₁
      (F : IndexedSplitFunctor C' D')
      where

      split-functor
        : (x : ChainCategory.Object C)
        → SplitFunctor
          (DependentCategory.category (indexed-category₁ C') x)
          (DependentCategory.category (indexed-category₁ D') x)
      split-functor x
        = indexed-split-functor₀
          (indexed-split-functor-tail F x)

      abstract

        split-functor-square
          : {x y : ChainCategory.Object C}
          → (f : ChainCategory.Arrow C x y)
          → SplitFunctorSquare
            (DependentCategory.functor (indexed-category₁ C') f)
            (DependentCategory.functor (indexed-category₁ D') f)
            (split-functor x)
            (split-functor y)
        split-functor-square f
          = indexed-split-functor-square₀
            (indexed-split-functor-indexed-split-functor-square F f)

    indexed-split-functor₁
      : IndexedSplitFunctor C' D'
      → SplitDependentFunctor
        (indexed-category₁ C')
        (indexed-category₁ D')
    indexed-split-functor₁ F
      = record {IndexedSplitFunctor₁ F}

  -- #### IndexedSplitFunctorSquare

  module _
    {C₁ C₂ : ChainCategory (suc zero)}
    {C₁' D₁' : IndexedCategory C₁}
    {C₂' D₂' : IndexedCategory C₂}
    {F : ChainFunctor C₁ C₂}
    {F' : IndexedFunctor C₁' C₂' F}
    {G' : IndexedFunctor D₁' D₂' F}
    {H₁ : IndexedSplitFunctor C₁' D₁'}
    {H₂ : IndexedSplitFunctor C₂' D₂'}
    where

    module IndexedSplitFunctorSquare₁
      (s : IndexedSplitFunctorSquare F' G' H₁ H₂)
      where

      functor
        : FunctorEqual
          (DependentFunctor.functor (indexed-functor₁ F'))
          (DependentFunctor.functor (indexed-functor₁ G'))
      functor
        = functor-refl

      split-functor
        : (x₁ : ChainCategory.Object C₁)
        → SplitFunctorSquare'
          (DependentFunctor.functor' (indexed-functor₁ F') x₁)
          (DependentFunctor.functor' (indexed-functor₁ G') x₁)
          (SplitDependentFunctor.split-functor (indexed-split-functor₁ H₁) x₁)
          (SplitDependentFunctor.split-functor (indexed-split-functor₁ H₂)
            (DependentFunctor.base (indexed-functor₁ F') x₁))
      split-functor x₁
        = split-functor-square'
        $ indexed-split-functor-square₀
          (indexed-split-functor-square-tail s x₁)

    indexed-split-functor-square₁
      : IndexedSplitFunctorSquare F' G' H₁ H₂
      → SplitDependentFunctorSquare
        (indexed-functor₁ F')
        (indexed-functor₁ G')
        (indexed-split-functor₁ H₁)
        (indexed-split-functor₁ H₂)
    indexed-split-functor-square₁ s
      = record {IndexedSplitFunctorSquare₁ s}

  -- ### Compose

  indexed-split-functor-compose
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' D' E' : IndexedCategory C}
    → IndexedSplitFunctor D' E'
    → IndexedSplitFunctor C' D'
    → IndexedSplitFunctor C' E'
  
  indexed-split-functor-square-compose
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory n}
    → {C₁' D₁' E₁' : IndexedCategory C₁}
    → {C₂' D₂' E₂' : IndexedCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → {F' : IndexedFunctor C₁' C₂' F}
    → {G' : IndexedFunctor D₁' D₂' F}
    → {H' : IndexedFunctor E₁' E₂' F}
    → {I₁ : IndexedSplitFunctor D₁' E₁'}
    → {I₂ : IndexedSplitFunctor D₂' E₂'}
    → {J₁ : IndexedSplitFunctor C₁' D₁'}
    → {J₂ : IndexedSplitFunctor C₂' D₂'}
    → IndexedSplitFunctorSquare G' H' I₁ I₂
    → IndexedSplitFunctorSquare F' G' J₁ J₂
    → IndexedSplitFunctorSquare F' H'
      (indexed-split-functor-compose I₁ J₁)
      (indexed-split-functor-compose I₂ J₂)

  indexed-split-functor-compose
    {n = zero} F G
    = nil
      (split-functor-compose
        (indexed-split-functor₀ F)
        (indexed-split-functor₀ G))
  indexed-split-functor-compose
    {n = suc _} F G
    = cons
      (λ x → indexed-split-functor-compose
        (indexed-split-functor-tail F x)
        (indexed-split-functor-tail G x))
      (λ f → indexed-split-functor-square-compose
        (indexed-split-functor-indexed-split-functor-square F f)
        (indexed-split-functor-indexed-split-functor-square G f))

  indexed-split-functor-square-compose
    {n = zero} s t
    = nil
      (split-functor-square-compose
        (indexed-split-functor-square₀ s)
        (indexed-split-functor-square₀ t))
  indexed-split-functor-square-compose
    {n = suc _} s t
    = cons
      (λ x₁ → indexed-split-functor-square-compose
        (indexed-split-functor-square-tail s x₁)
        (indexed-split-functor-square-tail t x₁))

-- ## Modules

-- ### IndexedSplitFunctor

IndexedSplitFunctor
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedCategory C
  → IndexedCategory C
  → Set
IndexedSplitFunctor
  = Internal.IndexedSplitFunctor
  
open Internal.IndexedSplitFunctor public

open Internal public
  using (indexed-split-functor₀; indexed-split-functor₁;
    indexed-split-functor-compose)

module IndexedSplitFunctor where

  open Internal public using () renaming
    ( indexed-split-functor-indexed-split-functor-square
      to indexed-split-functor-square
    ; indexed-split-functor-tail
      to tail
    )

-- ### IndexedSplitFunctorSquare

IndexedSplitFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' D₁' : IndexedCategory C₁}
  → {C₂' D₂' : IndexedCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → IndexedFunctor C₁' C₂' F
  → IndexedFunctor D₁' D₂' F
  → IndexedSplitFunctor C₁' D₁'
  → IndexedSplitFunctor C₂' D₂'
  → Set
IndexedSplitFunctorSquare
  = Internal.IndexedSplitFunctorSquare
  
open Internal.IndexedSplitFunctorSquare public

open Internal public
  using (indexed-split-functor-square₀; indexed-split-functor-square₁)

module IndexedSplitFunctorSquare where

  open Internal public using () renaming
    ( indexed-split-functor-square-tail
      to tail
    )

