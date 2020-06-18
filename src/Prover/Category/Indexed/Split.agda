module Prover.Category.Indexed.Split where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; FunctorEqual;
    functor-refl)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedFunctor; indexed-category₀; indexed-dependent-category₀;
    indexed-dependent-functor₀; indexed-functor₀)
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
  
  -- #### IndexedSplitDependentFunctor
  
  record IndexedSplitDependentFunctor
    {n : ℕ}
    {C : Category}
    {C' : ChainDependentCategory C n}
    (C'' D'' : IndexedDependentCategory C')
    : Set
  
  -- #### IndexedSplitDependentFunctorSquare
  
  record IndexedSplitDependentFunctorSquare
    {n : ℕ}
    {C₁ C₂ : Category}
    {C₁' : ChainDependentCategory C₁ n}
    {C₂' : ChainDependentCategory C₂ n}
    {C₁'' D₁'' : IndexedDependentCategory C₁'}
    {C₂'' D₂'' : IndexedDependentCategory C₂'}
    {F : ChainDependentFunctor C₁' C₂'}
    (F' : IndexedDependentFunctor C₁'' C₂'' F)
    (G' : IndexedDependentFunctor D₁'' D₂'' F)
    (H₁ : IndexedSplitDependentFunctor C₁'' D₁'')
    (H₂ : IndexedSplitDependentFunctor C₂'' D₂'')
    : Set
  
  -- ### Interface
  
  -- #### IndexedSplitFunctor
  
  indexed-split-functor₀
    : {C : ChainCategory zero}
    → {C' D' : IndexedCategory C}
    → IndexedSplitFunctor C' D'
    → SplitFunctor
      (indexed-category₀ C')
      (indexed-category₀ D')
  
  indexed-split-functor-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : IndexedCategory C}
    → IndexedSplitFunctor C' D'
    → IndexedSplitDependentFunctor
      (IndexedCategory.unpack C')
      (IndexedCategory.unpack D')

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
  
  indexed-split-functor-square-unpack
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
    → IndexedSplitDependentFunctorSquare
      (IndexedFunctor.unpack F')
      (IndexedFunctor.unpack G')
      (indexed-split-functor-unpack H₁)
      (indexed-split-functor-unpack H₂)

  -- ### Definitions
  
  -- #### IndexedSplitFunctor
  
  data IndexedSplitFunctor where
    
    empty
      : {C : ChainCategory zero}
      → {C' D' : IndexedCategory C}
      → SplitFunctor
        (indexed-category₀ C')
        (indexed-category₀ D')
      → IndexedSplitFunctor C' D'

    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' D' : IndexedCategory C}
      → IndexedSplitDependentFunctor
        (IndexedCategory.unpack C')
        (IndexedCategory.unpack D')
      → IndexedSplitFunctor C' D'
  
  indexed-split-functor₀ (empty F)
    = F
  
  indexed-split-functor-unpack (sigma F)
    = F
  
  -- #### IndexedSplitFunctorSquare
  
  data IndexedSplitFunctorSquare where
  
    empty
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

    sigma
      : {n : ℕ}
      → {C₁ C₂ : ChainCategory (suc n)}
      → {C₁' D₁' : IndexedCategory C₁}
      → {C₂' D₂' : IndexedCategory C₂}
      → {F : ChainFunctor C₁ C₂}
      → {F' : IndexedFunctor C₁' C₂' F}
      → {G' : IndexedFunctor D₁' D₂' F}
      → {H₁ : IndexedSplitFunctor C₁' D₁'}
      → {H₂ : IndexedSplitFunctor C₂' D₂'}
      → IndexedSplitDependentFunctorSquare
        (IndexedFunctor.unpack F')
        (IndexedFunctor.unpack G')
        (indexed-split-functor-unpack H₁)
        (indexed-split-functor-unpack H₂)
      → IndexedSplitFunctorSquare F' G' H₁ H₂
  
  indexed-split-functor-square₀ (empty s)
    = s

  indexed-split-functor-square-unpack (sigma s)
    = s

  -- #### IndexedSplitDependentFunctor
  
  record IndexedSplitDependentFunctor
    {_ C} C'' D''
    where

    inductive

    no-eta-equality

    constructor
      
      indexed-split-dependent-functor

    field

      indexed-split-functor
        : (x : Category.Object C)
        → IndexedSplitFunctor
          (IndexedDependentCategory.indexed-category C'' x)
          (IndexedDependentCategory.indexed-category D'' x)

      indexed-split-functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → IndexedSplitFunctorSquare
          (IndexedDependentCategory.indexed-functor C'' f)
          (IndexedDependentCategory.indexed-functor D'' f)
          (indexed-split-functor x)
          (indexed-split-functor y)

  -- #### IndexedSplitDependentFunctorSquare
  
  record IndexedSplitDependentFunctorSquare
    {_ C₁ _ _ _ _ _ _ _ F} F' G' H₁ H₂
    where

    inductive

    constructor

      indexed-split-dependent-functor-square

    field

      indexed-split-functor
        : (x₁ : Category.Object C₁)
        → IndexedSplitFunctorSquare
          (IndexedDependentFunctor.indexed-functor F' x₁)
          (IndexedDependentFunctor.indexed-functor G' x₁)
          (IndexedSplitDependentFunctor.indexed-split-functor H₁ x₁)
          (IndexedSplitDependentFunctor.indexed-split-functor H₂
            (ChainDependentFunctor.base F x₁))

  -- ### Destruction

  -- #### IndexedSplitDependentFunctor

  module _ 
    {C : Category}
    {C' : ChainDependentCategory C zero}
    {C'' D'' : IndexedDependentCategory C'}
    where

    module IndexedSplitDependentFunctor₀
      (F : IndexedSplitDependentFunctor C'' D'')
      where

      split-functor
        : (x : Category.Object C)
        → SplitFunctor
          (DependentCategory.category (indexed-dependent-category₀ C'') x)
          (DependentCategory.category (indexed-dependent-category₀ D'') x)
      split-functor x
        = indexed-split-functor₀
          (IndexedSplitDependentFunctor.indexed-split-functor F x)
  
      abstract

        split-functor-square
          : {x y : Category.Object C}
          → (f : Category.Arrow C x y)
          → SplitFunctorSquare
            (DependentCategory.functor (indexed-dependent-category₀ C'') f)
            (DependentCategory.functor (indexed-dependent-category₀ D'') f)
            (split-functor x)
            (split-functor y)
        split-functor-square f
          = indexed-split-functor-square₀
            (IndexedSplitDependentFunctor.indexed-split-functor-square F f)

    indexed-split-dependent-functor₀
      : IndexedSplitDependentFunctor C'' D''
      → SplitDependentFunctor
        (indexed-dependent-category₀ C'') 
        (indexed-dependent-category₀ D'') 
    indexed-split-dependent-functor₀ F
      = record {IndexedSplitDependentFunctor₀ F}

  -- #### IndexedSplitDependentFunctorSquare

  module _
    {C₁ C₂ : Category}
    {C₁' : ChainDependentCategory C₁ zero}
    {C₂' : ChainDependentCategory C₂ zero}
    {C₁'' D₁'' : IndexedDependentCategory C₁'}
    {C₂'' D₂'' : IndexedDependentCategory C₂'}
    {F : ChainDependentFunctor C₁' C₂'}
    {F' : IndexedDependentFunctor C₁'' C₂'' F}
    {G' : IndexedDependentFunctor D₁'' D₂'' F}
    {H₁ : IndexedSplitDependentFunctor C₁'' D₁''}
    {H₂ : IndexedSplitDependentFunctor C₂'' D₂''}
    where

    module IndexedSplitDependentFunctorSquare₀
      (s : IndexedSplitDependentFunctorSquare F' G' H₁ H₂)
      where

      functor
        : FunctorEqual
          (DependentFunctor.functor
            (indexed-dependent-functor₀ F'))
          (DependentFunctor.functor
            (indexed-dependent-functor₀ G'))
      functor
        = functor-refl
  
      split-functor
        : (x₁ : Category.Object C₁)
        → SplitFunctorSquare'
          (DependentFunctor.functor'
            (indexed-dependent-functor₀ F') x₁)
          (DependentFunctor.functor'
            (indexed-dependent-functor₀ G') x₁)
          (SplitDependentFunctor.split-functor
            (indexed-split-dependent-functor₀ H₁) x₁)
          (SplitDependentFunctor.split-functor
            (indexed-split-dependent-functor₀ H₂)
            (DependentFunctor.base
              (indexed-dependent-functor₀ F') x₁))
      split-functor x₁
        = split-functor-square'
          (indexed-split-functor-square₀
            (IndexedSplitDependentFunctorSquare.indexed-split-functor s x₁))

    indexed-split-dependent-functor-square₀
      : IndexedSplitDependentFunctorSquare F' G' H₁ H₂
      → SplitDependentFunctorSquare
        (indexed-dependent-functor₀ F')
        (indexed-dependent-functor₀ G')
        (indexed-split-dependent-functor₀ H₁)
        (indexed-split-dependent-functor₀ H₂)
    indexed-split-dependent-functor-square₀ s
      = record {IndexedSplitDependentFunctorSquare₀ s}

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
  
  indexed-split-dependent-functor-compose
    : {n : ℕ}
    → {C : Category}
    → {C' : ChainDependentCategory C n}
    → {C'' D'' E'' : IndexedDependentCategory C'}
    → IndexedSplitDependentFunctor D'' E''
    → IndexedSplitDependentFunctor C'' D''
    → IndexedSplitDependentFunctor C'' E''
  
  indexed-split-dependent-functor-square-compose
    : {n : ℕ}
    → {C₁ C₂ : Category}
    → {C₁' : ChainDependentCategory C₁ n}
    → {C₂' : ChainDependentCategory C₂ n}
    → {C₁'' D₁'' E₁'' : IndexedDependentCategory C₁'}
    → {C₂'' D₂'' E₂'' : IndexedDependentCategory C₂'}
    → {F : ChainDependentFunctor C₁' C₂'}
    → {F' : IndexedDependentFunctor C₁'' C₂'' F}
    → {G' : IndexedDependentFunctor D₁'' D₂'' F}
    → {H' : IndexedDependentFunctor E₁'' E₂'' F}
    → {I₁ : IndexedSplitDependentFunctor D₁'' E₁''}
    → {I₂ : IndexedSplitDependentFunctor D₂'' E₂''}
    → {J₁ : IndexedSplitDependentFunctor C₁'' D₁''}
    → {J₂ : IndexedSplitDependentFunctor C₂'' D₂''}
    → IndexedSplitDependentFunctorSquare G' H' I₁ I₂
    → IndexedSplitDependentFunctorSquare F' G' J₁ J₂
    → IndexedSplitDependentFunctorSquare F' H'
      (indexed-split-dependent-functor-compose I₁ J₁)
      (indexed-split-dependent-functor-compose I₂ J₂)

  indexed-split-functor-compose {n = zero} F G
    = empty
      (split-functor-compose
        (indexed-split-functor₀ F)
        (indexed-split-functor₀ G))
  indexed-split-functor-compose {n = suc _} F G
    = sigma
      (indexed-split-dependent-functor-compose
        (indexed-split-functor-unpack F)
        (indexed-split-functor-unpack G))

  indexed-split-functor-square-compose {n = zero} s t
    = empty
      (split-functor-square-compose
        (indexed-split-functor-square₀ s)
        (indexed-split-functor-square₀ t))
  indexed-split-functor-square-compose {n = suc _} s t
    = sigma
      (indexed-split-dependent-functor-square-compose
        (indexed-split-functor-square-unpack s)
        (indexed-split-functor-square-unpack t))

  indexed-split-dependent-functor-compose F G
    = indexed-split-dependent-functor
      (λ x → indexed-split-functor-compose
        (IndexedSplitDependentFunctor.indexed-split-functor F x)
        (IndexedSplitDependentFunctor.indexed-split-functor G x))
      (λ f → indexed-split-functor-square-compose
        (IndexedSplitDependentFunctor.indexed-split-functor-square F f)
        (IndexedSplitDependentFunctor.indexed-split-functor-square G f))
  
  indexed-split-dependent-functor-square-compose s t
    = indexed-split-dependent-functor-square
      (λ x₁ → indexed-split-functor-square-compose
        (IndexedSplitDependentFunctorSquare.indexed-split-functor s x₁)
        (IndexedSplitDependentFunctorSquare.indexed-split-functor t x₁))

  -- ### Tail

  indexed-split-functor-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : IndexedCategory C}
    → IndexedSplitFunctor C' D'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSplitFunctor
      (IndexedCategory.tail C' x)
      (IndexedCategory.tail D' x)
  indexed-split-functor-tail F x
    = IndexedSplitDependentFunctor.indexed-split-functor
      (indexed-split-functor-unpack F) x

-- ## Modules

open Internal public
  using (IndexedSplitDependentFunctor; IndexedSplitDependentFunctorSquare;
    indexed-split-dependent-functor; indexed-split-dependent-functor₀;
    indexed-split-dependent-functor-compose;
    indexed-split-dependent-functor-square;
    indexed-split-dependent-functor-square₀;
    indexed-split-dependent-functor-square-compose)

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
  using (indexed-split-functor₀; indexed-split-functor-compose)

module IndexedSplitFunctor where

  open Internal.IndexedSplitFunctor public

  open Internal public using () renaming
    ( indexed-split-functor-tail
      to tail
    ; indexed-split-functor-unpack
      to unpack
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
  using (indexed-split-functor-square₀; indexed-split-functor-square-compose)

module IndexedSplitFunctorSquare where

  open Internal.IndexedSplitFunctorSquare public

  open Internal public using () renaming
    ( indexed-split-functor-square-unpack
      to unpack
    )

