module Prover.Category.Indexed.Simple where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Base
  using (Function; FunctionCompose; FunctionIdentity; FunctionSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Partial.Base
  using (PartialFunction)
open import Prover.Category.Partial.Base.Compose
  using (partial-function-compose)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types
  
  -- #### IndexedSimpleCategory
  
  data IndexedSimpleCategory
    : {n : ℕ}
    → ChainCategory n
    → Set₁
  
  -- #### IndexedSimpleFunctor
  
  data IndexedSimpleFunctor
    : {n : ℕ}
    → {C D : ChainCategory n}
    → IndexedSimpleCategory C
    → IndexedSimpleCategory D
    → ChainFunctor C D
    → Set
  
  -- #### IndexedSimpleFunctorIdentity
  
  data IndexedSimpleFunctorIdentity
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory n}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → IndexedSimpleFunctor C₁' C₂' F
    → Set
  
  -- #### IndexedSimpleFunctorCompose
  
  data IndexedSimpleFunctorCompose
    : {n : ℕ}
    → {C D E₁ E₂ : ChainCategory n}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {E₁' : IndexedSimpleCategory E₁}
    → {E₂' : IndexedSimpleCategory E₂}
    → {F : ChainFunctor D E₁}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E₂}
    → IndexedSimpleFunctor D' E₁' F
    → IndexedSimpleFunctor C' D' G
    → IndexedSimpleFunctor C' E₂' H
    → Set
  
  -- #### IndexedSimpleFunctorSquare
  
  data IndexedSimpleFunctorSquare
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {D₁' : IndexedSimpleCategory D₁}
    → {D₂' : IndexedSimpleCategory D₂}
    → {D₃' : IndexedSimpleCategory D₃}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₃}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → (F' : IndexedSimpleFunctor C₁' C₂' F)
    → (G' : IndexedSimpleFunctor D₁' D₃' G)
    → (H₁' : IndexedSimpleFunctor C₁' D₁' H₁)
    → (H₂' : IndexedSimpleFunctor C₂' D₂' H₂)
    → Set
    
  -- #### IndexedSimpleDependentCategory
  
  record IndexedSimpleDependentCategory
    {n : ℕ}
    {C : Category}
    (C' : ChainDependentCategory C n)
    : Set₁
  
  -- #### IndexedSimpleDependentFunctor
  
  record IndexedSimpleDependentFunctor
    {n : ℕ}
    {C D : Category}
    {C' : ChainDependentCategory C n}
    {D' : ChainDependentCategory D n}
    (C'' : IndexedSimpleDependentCategory C')
    (D'' : IndexedSimpleDependentCategory D')
    (F : ChainDependentFunctor C' D')
    : Set
    
  -- #### IndexedSimpleDependentFunctorIdentity
  
  record IndexedSimpleDependentFunctorIdentity
    {n : ℕ}
    {C : Category}
    {C' : ChainDependentCategory C n}
    {C'' : IndexedSimpleDependentCategory C'}
    {F : ChainDependentFunctor C' C'}
    (F' : IndexedSimpleDependentFunctor C'' C'' F)
    : Set
    
  -- #### IndexedSimpleDependentFunctorCompose
  
  record IndexedSimpleDependentFunctorCompose
    {n : ℕ}
    {C D E : Category}
    {C' : ChainDependentCategory C n}
    {D' : ChainDependentCategory D n}
    {E' : ChainDependentCategory E n}
    {C'' : IndexedSimpleDependentCategory C'}
    {D'' : IndexedSimpleDependentCategory D'}
    {E'' : IndexedSimpleDependentCategory E'}
    {F : ChainDependentFunctor D' E'}
    {G : ChainDependentFunctor C' D'}
    {H : ChainDependentFunctor C' E'}
    (F' : IndexedSimpleDependentFunctor D'' E'' F)
    (G' : IndexedSimpleDependentFunctor C'' D'' G)
    (H' : IndexedSimpleDependentFunctor C'' E'' H)
    : Set
  
  -- #### IndexedSimpleDependentFunctorSquare
  
  record IndexedSimpleDependentFunctorSquare
    {n : ℕ}
    {C₁ C₂ D₁ D₂ : Category}
    {C₁' : ChainDependentCategory C₁ n}
    {C₂' : ChainDependentCategory C₂ n}
    {D₁' : ChainDependentCategory D₁ n}
    {D₂' : ChainDependentCategory D₂ n}
    {C₁'' : IndexedSimpleDependentCategory C₁'}
    {C₂'' : IndexedSimpleDependentCategory C₂'}
    {D₁'' : IndexedSimpleDependentCategory D₁'}
    {D₂'' : IndexedSimpleDependentCategory D₂'}
    {F : ChainDependentFunctor C₁' C₂'}
    {G : ChainDependentFunctor D₁' D₂'}
    {H₁ : ChainDependentFunctor C₁' D₁'}
    {H₂ : ChainDependentFunctor C₂' D₂'}
    (F' : IndexedSimpleDependentFunctor C₁'' C₂'' F)
    (G' : IndexedSimpleDependentFunctor D₁'' D₂'' G)
    (H₁' : IndexedSimpleDependentFunctor C₁'' D₁'' H₁)
    (H₂' : IndexedSimpleDependentFunctor C₂'' D₂'' H₂)
    : Set
    
  -- ### Interface

  -- #### IndexedSimpleCategory

  indexed-simple-category₀
    : {C : ChainCategory zero}
    → IndexedSimpleCategory C
    → Set
  
  indexed-simple-category-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSimpleCategory C
    → IndexedSimpleDependentCategory
      (ChainCategory.unpack C)

  -- #### IndexedSimpleFunctor

  indexed-simple-functor₀
    : {C D : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {F : ChainFunctor C D}
    → IndexedSimpleFunctor C' D' F
    → Function
      (indexed-simple-category₀ C')
      (indexed-simple-category₀ D')

  indexed-simple-functor-unpack
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {F : ChainFunctor C D}
    → IndexedSimpleFunctor C' D' F
    → IndexedSimpleDependentFunctor
      (indexed-simple-category-unpack C')
      (indexed-simple-category-unpack D')
      (ChainFunctor.unpack F)

  -- #### IndexedSimpleFunctorIdentity

  indexed-simple-functor-identity₀
    : {C : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedSimpleFunctor C' C' F}
    → IndexedSimpleFunctorIdentity F'
    → FunctionIdentity
      (indexed-simple-functor₀ F')

  indexed-simple-functor-identity-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedSimpleFunctor C' C' F}
    → IndexedSimpleFunctorIdentity F'
    → IndexedSimpleDependentFunctorIdentity
      (indexed-simple-functor-unpack F')

  -- #### IndexedSimpleFunctorCompose

  indexed-simple-functor-compose₀
    : {C D E : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {E' : IndexedSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : IndexedSimpleFunctor D' E' F}
    → {G' : IndexedSimpleFunctor C' D' G}
    → {H' : IndexedSimpleFunctor C' E' H}
    → IndexedSimpleFunctorCompose F' G' H'
    → FunctionCompose
      (indexed-simple-functor₀ F')
      (indexed-simple-functor₀ G')
      (indexed-simple-functor₀ H')

  indexed-simple-functor-compose-unpack
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {E' : IndexedSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : IndexedSimpleFunctor D' E' F}
    → {G' : IndexedSimpleFunctor C' D' G}
    → {H' : IndexedSimpleFunctor C' E' H}
    → IndexedSimpleFunctorCompose F' G' H'
    → IndexedSimpleDependentFunctorCompose
      (indexed-simple-functor-unpack F')
      (indexed-simple-functor-unpack G')
      (indexed-simple-functor-unpack H')

  -- #### IndexedSimpleFunctorSquare

  indexed-simple-functor-square₀
    : {C₁ C₂ D₁ D₂ : ChainCategory zero}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {D₁' : IndexedSimpleCategory D₁}
    → {D₂' : IndexedSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : IndexedSimpleFunctor C₁' C₂' F}
    → {G' : IndexedSimpleFunctor D₁' D₂' G}
    → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
    → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
    → IndexedSimpleFunctorSquare F' G' H₁' H₂'
    → FunctionSquare
      (indexed-simple-functor₀ F')
      (indexed-simple-functor₀ G')
      (indexed-simple-functor₀ H₁')
      (indexed-simple-functor₀ H₂')

  indexed-simple-functor-square-unpack
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {D₁' : IndexedSimpleCategory D₁}
    → {D₂' : IndexedSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : IndexedSimpleFunctor C₁' C₂' F}
    → {G' : IndexedSimpleFunctor D₁' D₂' G}
    → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
    → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
    → IndexedSimpleFunctorSquare F' G' H₁' H₂'
    → IndexedSimpleDependentFunctorSquare
      (indexed-simple-functor-unpack F')
      (indexed-simple-functor-unpack G')
      (indexed-simple-functor-unpack H₁')
      (indexed-simple-functor-unpack H₂')

  -- ### Definitions
  
  -- #### IndexedSimpleCategory
  
  data IndexedSimpleCategory where
  
    empty
      : {C : ChainCategory zero}
      → Set
      → IndexedSimpleCategory C
  
    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → IndexedSimpleDependentCategory
        (ChainCategory.unpack C)
      → IndexedSimpleCategory C
  
  indexed-simple-category₀ (empty A)
    = A

  indexed-simple-category-unpack (sigma A)
    = A

  -- #### IndexedSimpleFunctor
  
  data IndexedSimpleFunctor where
  
    empty
      : {C D : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {F : ChainFunctor C D}
      → Function
        (indexed-simple-category₀ C')
        (indexed-simple-category₀ D')
      → IndexedSimpleFunctor C' D' F
  
    sigma
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {F : ChainFunctor C D}
      → IndexedSimpleDependentFunctor
        (indexed-simple-category-unpack C')
        (indexed-simple-category-unpack D')
        (ChainFunctor.unpack F)
      → IndexedSimpleFunctor C' D' F
  
  indexed-simple-functor₀ (empty f)
    = f

  indexed-simple-functor-unpack (sigma f)
    = f

  -- #### IndexedSimpleFunctorIdentity
  
  data IndexedSimpleFunctorIdentity where
  
    empty
      : {C : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedSimpleFunctor C' C' F}
      → FunctionIdentity
        (indexed-simple-functor₀ F')
      → IndexedSimpleFunctorIdentity F'
  
    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedSimpleFunctor C' C' F}
      → IndexedSimpleDependentFunctorIdentity
        (indexed-simple-functor-unpack F')
      → IndexedSimpleFunctorIdentity F'
  
  indexed-simple-functor-identity₀ (empty p)
    = p

  indexed-simple-functor-identity-unpack (sigma p)
    = p

  -- #### IndexedSimpleFunctorCompose
  
  data IndexedSimpleFunctorCompose where
  
    empty
      : {C D E : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {E' : IndexedSimpleCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : IndexedSimpleFunctor D' E' F}
      → {G' : IndexedSimpleFunctor C' D' G}
      → {H' : IndexedSimpleFunctor C' E' H}
      → FunctionCompose
        (indexed-simple-functor₀ F')
        (indexed-simple-functor₀ G')
        (indexed-simple-functor₀ H')
      → IndexedSimpleFunctorCompose F' G' H'
  
    sigma
      : {n : ℕ}
      → {C D E : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {E' : IndexedSimpleCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : IndexedSimpleFunctor D' E' F}
      → {G' : IndexedSimpleFunctor C' D' G}
      → {H' : IndexedSimpleFunctor C' E' H}
      → IndexedSimpleDependentFunctorCompose
        (indexed-simple-functor-unpack F')
        (indexed-simple-functor-unpack G')
        (indexed-simple-functor-unpack H')
      → IndexedSimpleFunctorCompose F' G' H'
  
  indexed-simple-functor-compose₀ (empty p)
    = p

  indexed-simple-functor-compose-unpack (sigma p)
    = p

  -- #### IndexedSimpleFunctorSquare
  
  data IndexedSimpleFunctorSquare where
  
    empty
      : {C₁ C₂ D₁ D₂ : ChainCategory zero}
      → {C₁' : IndexedSimpleCategory C₁}
      → {C₂' : IndexedSimpleCategory C₂}
      → {D₁' : IndexedSimpleCategory D₁}
      → {D₂' : IndexedSimpleCategory D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : IndexedSimpleFunctor C₁' C₂' F}
      → {G' : IndexedSimpleFunctor D₁' D₂' G}
      → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
      → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
      → FunctionSquare
        (indexed-simple-functor₀ F')
        (indexed-simple-functor₀ G')
        (indexed-simple-functor₀ H₁')
        (indexed-simple-functor₀ H₂')
      → IndexedSimpleFunctorSquare F' G' H₁' H₂'
  
    sigma
      : {n : ℕ}
      → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
      → {C₁' : IndexedSimpleCategory C₁}
      → {C₂' : IndexedSimpleCategory C₂}
      → {D₁' : IndexedSimpleCategory D₁}
      → {D₂' : IndexedSimpleCategory D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : IndexedSimpleFunctor C₁' C₂' F}
      → {G' : IndexedSimpleFunctor D₁' D₂' G}
      → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
      → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
      → IndexedSimpleDependentFunctorSquare
        (indexed-simple-functor-unpack F')
        (indexed-simple-functor-unpack G')
        (indexed-simple-functor-unpack H₁')
        (indexed-simple-functor-unpack H₂')
      → IndexedSimpleFunctorSquare F' G' H₁' H₂'
  
  indexed-simple-functor-square₀ (empty s)
    = s

  indexed-simple-functor-square-unpack (sigma s)
    = s

  -- #### IndexedSimpleDependentCategory
  
  record IndexedSimpleDependentCategory {_ C} C' where
  
    inductive
  
    no-eta-equality
  
    constructor

      indexed-simple-dependent-category

    field
  
      indexed-simple-category
        : (x : Category.Object C)
        → IndexedSimpleCategory
          (ChainDependentCategory.chain-category C' x)
  
      indexed-simple-functor
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → IndexedSimpleFunctor
          (indexed-simple-category x)
          (indexed-simple-category y)
          (ChainDependentCategory.chain-functor C' f)
  
      indexed-simple-functor-identity
        : (x : Category.Object C)
        → IndexedSimpleFunctorIdentity
          (indexed-simple-functor (Category.identity C x))
  
      indexed-simple-functor-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → IndexedSimpleFunctorCompose
          (indexed-simple-functor f)
          (indexed-simple-functor g)
          (indexed-simple-functor (Category.compose C f g))
  
  -- #### IndexedSimpleDependentFunctor
  
  record IndexedSimpleDependentFunctor
    {_ C} C'' D'' F
    where

    inductive

    no-eta-equality

    constructor
    
      indexed-simple-dependent-functor

    field

      indexed-simple-functor
        : (x : Category.Object C)
        → IndexedSimpleFunctor
          (IndexedSimpleDependentCategory.indexed-simple-category C'' x)
          (IndexedSimpleDependentCategory.indexed-simple-category D''
            (ChainDependentFunctor.base F x))
          (ChainDependentFunctor.chain-functor F x)

      indexed-simple-functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → IndexedSimpleFunctorSquare
          (IndexedSimpleDependentCategory.indexed-simple-functor C'' f)
          (IndexedSimpleDependentCategory.indexed-simple-functor D''
            (ChainDependentFunctor.map F f))
          (indexed-simple-functor x)
          (indexed-simple-functor y)

  -- #### IndexedSimpleDependentFunctorIdentity
  
  record IndexedSimpleDependentFunctorIdentity
    {_ C _ _ F} F'
    where

    inductive

    constructor

      indexed-simple-dependent-functor-identity

    field

      functor
        : FunctorIdentity
          (ChainDependentFunctor.functor F)
  
    open FunctorIdentity functor public

    field

      indexed-simple-functor
        : (x : Category.Object C)
        → IndexedSimpleFunctorIdentity
          (IndexedSimpleDependentFunctor.indexed-simple-functor F' x)

  -- #### IndexedSimpleDependentFunctorCompose
  
  record IndexedSimpleDependentFunctorCompose
    {_ C _ _ _ _ _ _ _ _ F G H} F' G' H'
    where
    
    inductive

    constructor

      indexed-simple-dependent-functor-compose

    field

      functor
        : FunctorCompose
          (ChainDependentFunctor.functor F)
          (ChainDependentFunctor.functor G)
          (ChainDependentFunctor.functor H)

    open FunctorCompose functor public
  
    field
  
      indexed-simple-functor
        : (x : Category.Object C)
        → IndexedSimpleFunctorCompose
          (IndexedSimpleDependentFunctor.indexed-simple-functor F'
            (ChainDependentFunctor.base G x))
          (IndexedSimpleDependentFunctor.indexed-simple-functor G' x)
          (IndexedSimpleDependentFunctor.indexed-simple-functor H' x)
  
  -- #### IndexedSimpleDependentFunctorSquare
  
  record IndexedSimpleDependentFunctorSquare
    {_ C₁ _ _ _ _ _ _ _ _ _ _ _ F G H₁ H₂} F' G' H₁' H₂'
    where

    inductive

    constructor

      indexed-simple-dependent-functor-square

    field

      functor
        : FunctorSquare
          (ChainDependentFunctor.functor F)
          (ChainDependentFunctor.functor G)
          (ChainDependentFunctor.functor H₁)
          (ChainDependentFunctor.functor H₂)
  
    open FunctorSquare functor public
  
    field
  
      indexed-simple-functor
        : (x₁ : Category.Object C₁)
        → IndexedSimpleFunctorSquare
          (IndexedSimpleDependentFunctor.indexed-simple-functor F' x₁)
          (IndexedSimpleDependentFunctor.indexed-simple-functor G'
            (ChainDependentFunctor.base H₁ x₁))
          (IndexedSimpleDependentFunctor.indexed-simple-functor H₁' x₁)
          (IndexedSimpleDependentFunctor.indexed-simple-functor H₂'
            (ChainDependentFunctor.base F x₁))
  
  -- ### Tail

  indexed-simple-category-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSimpleCategory C
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSimpleCategory (ChainCategory.tail C x)
  indexed-simple-category-tail C' x
    = IndexedSimpleDependentCategory.indexed-simple-category
      (indexed-simple-category-unpack C') x

-- ## Modules

open Internal public
  using (IndexedSimpleDependentCategory; IndexedSimpleDependentFunctor;
    IndexedSimpleDependentFunctorCompose; IndexedSimpleDependentFunctorIdentity;
    IndexedSimpleDependentFunctorSquare; indexed-simple-dependent-category;
    indexed-simple-dependent-functor; indexed-simple-dependent-functor-compose;
    indexed-simple-dependent-functor-identity;
    indexed-simple-dependent-functor-square)

-- ### IndexedSimpleCategory

IndexedSimpleCategory
  : {n : ℕ}
  → ChainCategory n
  → Set₁
IndexedSimpleCategory
  = Internal.IndexedSimpleCategory

open Internal.IndexedSimpleCategory public

open Internal public
  using (indexed-simple-category₀)

module IndexedSimpleCategory where

  open Internal.IndexedSimpleCategory public

  open Internal public using () renaming
    ( indexed-simple-category-tail
      to tail
    ; indexed-simple-category-unpack
      to unpack
    )

-- ### IndexedSimpleFunctor

IndexedSimpleFunctor
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → IndexedSimpleCategory C₁
  → IndexedSimpleCategory C₂
  → ChainFunctor C₁ C₂
  → Set
IndexedSimpleFunctor
  = Internal.IndexedSimpleFunctor

open Internal.IndexedSimpleFunctor public

open Internal public
  using (indexed-simple-functor₀)

module IndexedSimpleFunctor where

  open Internal.IndexedSimpleFunctor public

  open Internal public using () renaming
    ( indexed-simple-functor-unpack
      to unpack
    )

-- ### IndexedSimpleFunctorIdentity

IndexedSimpleFunctorIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : IndexedSimpleCategory C₁}
  → {C₂' : IndexedSimpleCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → IndexedSimpleFunctor C₁' C₂' F
  → Set
IndexedSimpleFunctorIdentity
  = Internal.IndexedSimpleFunctorIdentity

open Internal.IndexedSimpleFunctorIdentity public

open Internal public
  using (indexed-simple-functor-identity₀)

module IndexedSimpleFunctorIdentity where

  open Internal.IndexedSimpleFunctorIdentity public

  open Internal public using () renaming
    ( indexed-simple-functor-identity-unpack
      to unpack
    )

-- ### IndexedSimpleFunctorCompose

IndexedSimpleFunctorCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → {D' : IndexedSimpleCategory D}
  → {E₁' : IndexedSimpleCategory E₁}
  → {E₂' : IndexedSimpleCategory E₂}
  → {F : ChainFunctor D E₁}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E₂}
  → IndexedSimpleFunctor D' E₁' F
  → IndexedSimpleFunctor C' D' G
  → IndexedSimpleFunctor C' E₂' H
  → Set
IndexedSimpleFunctorCompose
  = Internal.IndexedSimpleFunctorCompose

open Internal.IndexedSimpleFunctorCompose public

open Internal public
  using (indexed-simple-functor-compose₀)

module IndexedSimpleFunctorCompose where

  open Internal.IndexedSimpleFunctorCompose public

  open Internal public using () renaming
    ( indexed-simple-functor-compose-unpack
      to unpack
    )

-- ### IndexedSimpleFunctorSquare

IndexedSimpleFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
  → {C₁' : IndexedSimpleCategory C₁}
  → {C₂' : IndexedSimpleCategory C₂}
  → {D₁' : IndexedSimpleCategory D₁}
  → {D₂' : IndexedSimpleCategory D₂}
  → {D₃' : IndexedSimpleCategory D₃}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₃}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → (F' : IndexedSimpleFunctor C₁' C₂' F)
  → (G' : IndexedSimpleFunctor D₁' D₃' G)
  → (H₁' : IndexedSimpleFunctor C₁' D₁' H₁)
  → (H₂' : IndexedSimpleFunctor C₂' D₂' H₂)
  → Set
IndexedSimpleFunctorSquare
  = Internal.IndexedSimpleFunctorSquare

open Internal.IndexedSimpleFunctorSquare public

open Internal public
  using (indexed-simple-functor-square₀)

module IndexedSimpleFunctorSquare where

  open Internal.IndexedSimpleFunctorSquare public

  open Internal public using () renaming
    ( indexed-simple-functor-square-unpack
      to unpack
    )

