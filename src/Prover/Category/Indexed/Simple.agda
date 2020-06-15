module Prover.Category.Indexed.Simple where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Simple
  using (Function; FunctionCompose; FunctionIdentity; FunctionSquare)
open import Prover.Category.Partial.Simple
  using (PartialFunction; partial-function-compose)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types
  
  -- #### IndexedSet
  
  data IndexedSet
    : {n : ℕ}
    → ChainCategory n
    → Set₁
  
  -- #### IndexedFunction
  
  data IndexedFunction
    : {n : ℕ}
    → {C D : ChainCategory n}
    → IndexedSet C
    → IndexedSet D
    → ChainFunctor C D
    → Set
  
  -- #### IndexedFunctionIdentity
  
  data IndexedFunctionIdentity
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory n}
    → {C₁' : IndexedSet C₁}
    → {C₂' : IndexedSet C₂}
    → {F : ChainFunctor C₁ C₂}
    → IndexedFunction C₁' C₂' F
    → Set
  
  -- #### IndexedFunctionCompose
  
  data IndexedFunctionCompose
    : {n : ℕ}
    → {C D E₁ E₂ : ChainCategory n}
    → {C' : IndexedSet C}
    → {D' : IndexedSet D}
    → {E₁' : IndexedSet E₁}
    → {E₂' : IndexedSet E₂}
    → {F : ChainFunctor D E₁}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E₂}
    → IndexedFunction D' E₁' F
    → IndexedFunction C' D' G
    → IndexedFunction C' E₂' H
    → Set
  
  -- #### IndexedFunctionSquare
  
  data IndexedFunctionSquare
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
    → {C₁' : IndexedSet C₁}
    → {C₂' : IndexedSet C₂}
    → {D₁' : IndexedSet D₁}
    → {D₂' : IndexedSet D₂}
    → {D₃' : IndexedSet D₃}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₃}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → (F' : IndexedFunction C₁' C₂' F)
    → (G' : IndexedFunction D₁' D₃' G)
    → (H₁' : IndexedFunction C₁' D₁' H₁)
    → (H₂' : IndexedFunction C₂' D₂' H₂)
    → Set
    
  -- #### IndexedDependentSet
  
  record IndexedDependentSet
    {n : ℕ}
    {C : Category}
    (C' : ChainDependentCategory C n)
    : Set₁
  
  -- #### IndexedDependentFunction
  
  record IndexedDependentFunction
    {n : ℕ}
    {C D : Category}
    {C' : ChainDependentCategory C n}
    {D' : ChainDependentCategory D n}
    (C'' : IndexedDependentSet C')
    (D'' : IndexedDependentSet D')
    (F : ChainDependentFunctor C' D')
    : Set
    
  -- #### IndexedDependentFunctionIdentity
  
  record IndexedDependentFunctionIdentity
    {n : ℕ}
    {C : Category}
    {C' : ChainDependentCategory C n}
    {C'' : IndexedDependentSet C'}
    {F : ChainDependentFunctor C' C'}
    (F' : IndexedDependentFunction C'' C'' F)
    : Set
    
  -- #### IndexedDependentFunctionCompose
  
  record IndexedDependentFunctionCompose
    {n : ℕ}
    {C D E : Category}
    {C' : ChainDependentCategory C n}
    {D' : ChainDependentCategory D n}
    {E' : ChainDependentCategory E n}
    {C'' : IndexedDependentSet C'}
    {D'' : IndexedDependentSet D'}
    {E'' : IndexedDependentSet E'}
    {F : ChainDependentFunctor D' E'}
    {G : ChainDependentFunctor C' D'}
    {H : ChainDependentFunctor C' E'}
    (F' : IndexedDependentFunction D'' E'' F)
    (G' : IndexedDependentFunction C'' D'' G)
    (H' : IndexedDependentFunction C'' E'' H)
    : Set
  
  -- #### IndexedDependentFunctionSquare
  
  record IndexedDependentFunctionSquare
    {n : ℕ}
    {C₁ C₂ D₁ D₂ : Category}
    {C₁' : ChainDependentCategory C₁ n}
    {C₂' : ChainDependentCategory C₂ n}
    {D₁' : ChainDependentCategory D₁ n}
    {D₂' : ChainDependentCategory D₂ n}
    {C₁'' : IndexedDependentSet C₁'}
    {C₂'' : IndexedDependentSet C₂'}
    {D₁'' : IndexedDependentSet D₁'}
    {D₂'' : IndexedDependentSet D₂'}
    {F : ChainDependentFunctor C₁' C₂'}
    {G : ChainDependentFunctor D₁' D₂'}
    {H₁ : ChainDependentFunctor C₁' D₁'}
    {H₂ : ChainDependentFunctor C₂' D₂'}
    (F' : IndexedDependentFunction C₁'' C₂'' F)
    (G' : IndexedDependentFunction D₁'' D₂'' G)
    (H₁' : IndexedDependentFunction C₁'' D₁'' H₁)
    (H₂' : IndexedDependentFunction C₂'' D₂'' H₂)
    : Set
    
  -- ### Interface

  -- #### IndexedSet

  indexed-set₀
    : {C : ChainCategory zero}
    → IndexedSet C
    → Set
  
  indexed-set-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSet C
    → IndexedDependentSet
      (ChainCategory.unpack C)

  -- #### IndexedFunction

  indexed-function₀
    : {C D : ChainCategory zero}
    → {C' : IndexedSet C}
    → {D' : IndexedSet D}
    → {F : ChainFunctor C D}
    → IndexedFunction C' D' F
    → Function
      (indexed-set₀ C')
      (indexed-set₀ D')

  indexed-function-unpack
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : IndexedSet C}
    → {D' : IndexedSet D}
    → {F : ChainFunctor C D}
    → IndexedFunction C' D' F
    → IndexedDependentFunction
      (indexed-set-unpack C')
      (indexed-set-unpack D')
      (ChainFunctor.unpack F)

  -- #### IndexedFunctionIdentity

  indexed-function-identity₀
    : {C : ChainCategory zero}
    → {C' : IndexedSet C}
    → {F : ChainFunctor C C}
    → {F' : IndexedFunction C' C' F}
    → IndexedFunctionIdentity F'
    → FunctionIdentity
      (indexed-function₀ F')

  indexed-function-identity-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSet C}
    → {F : ChainFunctor C C}
    → {F' : IndexedFunction C' C' F}
    → IndexedFunctionIdentity F'
    → IndexedDependentFunctionIdentity
      (indexed-function-unpack F')

  -- #### IndexedFunctionCompose

  indexed-function-compose₀
    : {C D E : ChainCategory zero}
    → {C' : IndexedSet C}
    → {D' : IndexedSet D}
    → {E' : IndexedSet E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : IndexedFunction D' E' F}
    → {G' : IndexedFunction C' D' G}
    → {H' : IndexedFunction C' E' H}
    → IndexedFunctionCompose F' G' H'
    → FunctionCompose
      (indexed-function₀ F')
      (indexed-function₀ G')
      (indexed-function₀ H')

  indexed-function-compose-unpack
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : IndexedSet C}
    → {D' : IndexedSet D}
    → {E' : IndexedSet E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : IndexedFunction D' E' F}
    → {G' : IndexedFunction C' D' G}
    → {H' : IndexedFunction C' E' H}
    → IndexedFunctionCompose F' G' H'
    → IndexedDependentFunctionCompose
      (indexed-function-unpack F')
      (indexed-function-unpack G')
      (indexed-function-unpack H')

  -- #### IndexedFunctionSquare

  indexed-function-square₀
    : {C₁ C₂ D₁ D₂ : ChainCategory zero}
    → {C₁' : IndexedSet C₁}
    → {C₂' : IndexedSet C₂}
    → {D₁' : IndexedSet D₁}
    → {D₂' : IndexedSet D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : IndexedFunction C₁' C₂' F}
    → {G' : IndexedFunction D₁' D₂' G}
    → {H₁' : IndexedFunction C₁' D₁' H₁}
    → {H₂' : IndexedFunction C₂' D₂' H₂}
    → IndexedFunctionSquare F' G' H₁' H₂'
    → FunctionSquare
      (indexed-function₀ F')
      (indexed-function₀ G')
      (indexed-function₀ H₁')
      (indexed-function₀ H₂')

  indexed-function-square-unpack
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : IndexedSet C₁}
    → {C₂' : IndexedSet C₂}
    → {D₁' : IndexedSet D₁}
    → {D₂' : IndexedSet D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : IndexedFunction C₁' C₂' F}
    → {G' : IndexedFunction D₁' D₂' G}
    → {H₁' : IndexedFunction C₁' D₁' H₁}
    → {H₂' : IndexedFunction C₂' D₂' H₂}
    → IndexedFunctionSquare F' G' H₁' H₂'
    → IndexedDependentFunctionSquare
      (indexed-function-unpack F')
      (indexed-function-unpack G')
      (indexed-function-unpack H₁')
      (indexed-function-unpack H₂')

  -- ### Definitions
  
  -- #### IndexedSet
  
  data IndexedSet where
  
    empty
      : {C : ChainCategory zero}
      → Set
      → IndexedSet C
  
    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → IndexedDependentSet
        (ChainCategory.unpack C)
      → IndexedSet C
  
  indexed-set₀ (empty A)
    = A

  indexed-set-unpack (sigma A)
    = A

  -- #### IndexedFunction
  
  data IndexedFunction where
  
    empty
      : {C D : ChainCategory zero}
      → {C' : IndexedSet C}
      → {D' : IndexedSet D}
      → {F : ChainFunctor C D}
      → Function
        (indexed-set₀ C')
        (indexed-set₀ D')
      → IndexedFunction C' D' F
  
    sigma
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → {C' : IndexedSet C}
      → {D' : IndexedSet D}
      → {F : ChainFunctor C D}
      → IndexedDependentFunction
        (indexed-set-unpack C')
        (indexed-set-unpack D')
        (ChainFunctor.unpack F)
      → IndexedFunction C' D' F
  
  indexed-function₀ (empty f)
    = f

  indexed-function-unpack (sigma f)
    = f

  -- #### IndexedFunctionIdentity
  
  data IndexedFunctionIdentity where
  
    empty
      : {C : ChainCategory zero}
      → {C' : IndexedSet C}
      → {F : ChainFunctor C C}
      → {F' : IndexedFunction C' C' F}
      → FunctionIdentity
        (indexed-function₀ F')
      → IndexedFunctionIdentity F'
  
    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedSet C}
      → {F : ChainFunctor C C}
      → {F' : IndexedFunction C' C' F}
      → IndexedDependentFunctionIdentity
        (indexed-function-unpack F')
      → IndexedFunctionIdentity F'
  
  indexed-function-identity₀ (empty p)
    = p

  indexed-function-identity-unpack (sigma p)
    = p

  -- #### IndexedFunctionCompose
  
  data IndexedFunctionCompose where
  
    empty
      : {C D E : ChainCategory zero}
      → {C' : IndexedSet C}
      → {D' : IndexedSet D}
      → {E' : IndexedSet E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : IndexedFunction D' E' F}
      → {G' : IndexedFunction C' D' G}
      → {H' : IndexedFunction C' E' H}
      → FunctionCompose
        (indexed-function₀ F')
        (indexed-function₀ G')
        (indexed-function₀ H')
      → IndexedFunctionCompose F' G' H'
  
    sigma
      : {n : ℕ}
      → {C D E : ChainCategory (suc n)}
      → {C' : IndexedSet C}
      → {D' : IndexedSet D}
      → {E' : IndexedSet E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : IndexedFunction D' E' F}
      → {G' : IndexedFunction C' D' G}
      → {H' : IndexedFunction C' E' H}
      → IndexedDependentFunctionCompose
        (indexed-function-unpack F')
        (indexed-function-unpack G')
        (indexed-function-unpack H')
      → IndexedFunctionCompose F' G' H'
  
  indexed-function-compose₀ (empty p)
    = p

  indexed-function-compose-unpack (sigma p)
    = p

  -- #### IndexedFunctionSquare
  
  data IndexedFunctionSquare where
  
    empty
      : {C₁ C₂ D₁ D₂ : ChainCategory zero}
      → {C₁' : IndexedSet C₁}
      → {C₂' : IndexedSet C₂}
      → {D₁' : IndexedSet D₁}
      → {D₂' : IndexedSet D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : IndexedFunction C₁' C₂' F}
      → {G' : IndexedFunction D₁' D₂' G}
      → {H₁' : IndexedFunction C₁' D₁' H₁}
      → {H₂' : IndexedFunction C₂' D₂' H₂}
      → FunctionSquare
        (indexed-function₀ F')
        (indexed-function₀ G')
        (indexed-function₀ H₁')
        (indexed-function₀ H₂')
      → IndexedFunctionSquare F' G' H₁' H₂'
  
    sigma
      : {n : ℕ}
      → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
      → {C₁' : IndexedSet C₁}
      → {C₂' : IndexedSet C₂}
      → {D₁' : IndexedSet D₁}
      → {D₂' : IndexedSet D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : IndexedFunction C₁' C₂' F}
      → {G' : IndexedFunction D₁' D₂' G}
      → {H₁' : IndexedFunction C₁' D₁' H₁}
      → {H₂' : IndexedFunction C₂' D₂' H₂}
      → IndexedDependentFunctionSquare
        (indexed-function-unpack F')
        (indexed-function-unpack G')
        (indexed-function-unpack H₁')
        (indexed-function-unpack H₂')
      → IndexedFunctionSquare F' G' H₁' H₂'
  
  indexed-function-square₀ (empty s)
    = s

  indexed-function-square-unpack (sigma s)
    = s

  -- #### IndexedDependentSet
  
  record IndexedDependentSet {_ C} C' where
  
    inductive
  
    no-eta-equality
  
    constructor

      indexed-dependent-set

    field
  
      indexed-set
        : (x : Category.Object C)
        → IndexedSet
          (ChainDependentCategory.chain-category C' x)
  
      indexed-function
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → IndexedFunction
          (indexed-set x)
          (indexed-set y)
          (ChainDependentCategory.chain-functor C' f)
  
      indexed-function-identity
        : (x : Category.Object C)
        → IndexedFunctionIdentity
          (indexed-function (Category.identity C x))
  
      indexed-function-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → IndexedFunctionCompose
          (indexed-function f)
          (indexed-function g)
          (indexed-function (Category.compose C f g))
  
  -- #### IndexedDependentFunction
  
  record IndexedDependentFunction
    {_ C} C'' D'' F
    where

    inductive

    no-eta-equality

    constructor
    
      indexed-dependent-function

    field

      indexed-function
        : (x : Category.Object C)
        → IndexedFunction
          (IndexedDependentSet.indexed-set C'' x)
          (IndexedDependentSet.indexed-set D''
            (ChainDependentFunctor.base F x))
          (ChainDependentFunctor.chain-functor F x)

      indexed-function-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → IndexedFunctionSquare
          (IndexedDependentSet.indexed-function C'' f)
          (IndexedDependentSet.indexed-function D''
            (ChainDependentFunctor.map F f))
          (indexed-function x)
          (indexed-function y)

  -- #### IndexedDependentFunctionIdentity
  
  record IndexedDependentFunctionIdentity
    {_ C _ _ F} F'
    where

    inductive

    constructor

      indexed-dependent-function-identity

    field

      functor
        : FunctorIdentity
          (ChainDependentFunctor.functor F)
  
    open FunctorIdentity functor public

    field

      indexed-function
        : (x : Category.Object C)
        → IndexedFunctionIdentity
          (IndexedDependentFunction.indexed-function F' x)

  -- #### IndexedDependentFunctionCompose
  
  record IndexedDependentFunctionCompose
    {_ C _ _ _ _ _ _ _ _ F G H} F' G' H'
    where
    
    inductive

    constructor

      indexed-dependent-function-compose

    field

      functor
        : FunctorCompose
          (ChainDependentFunctor.functor F)
          (ChainDependentFunctor.functor G)
          (ChainDependentFunctor.functor H)

    open FunctorCompose functor public
  
    field
  
      indexed-function
        : (x : Category.Object C)
        → IndexedFunctionCompose
          (IndexedDependentFunction.indexed-function F'
            (ChainDependentFunctor.base G x))
          (IndexedDependentFunction.indexed-function G' x)
          (IndexedDependentFunction.indexed-function H' x)
  
  -- #### IndexedDependentFunctionSquare
  
  record IndexedDependentFunctionSquare
    {_ C₁ _ _ _ _ _ _ _ _ _ _ _ F G H₁ H₂} F' G' H₁' H₂'
    where

    inductive

    constructor

      indexed-dependent-function-square

    field

      functor
        : FunctorSquare
          (ChainDependentFunctor.functor F)
          (ChainDependentFunctor.functor G)
          (ChainDependentFunctor.functor H₁)
          (ChainDependentFunctor.functor H₂)
  
    open FunctorSquare functor public
  
    field
  
      indexed-function
        : (x₁ : Category.Object C₁)
        → IndexedFunctionSquare
          (IndexedDependentFunction.indexed-function F' x₁)
          (IndexedDependentFunction.indexed-function G'
            (ChainDependentFunctor.base H₁ x₁))
          (IndexedDependentFunction.indexed-function H₁' x₁)
          (IndexedDependentFunction.indexed-function H₂'
            (ChainDependentFunctor.base F x₁))
  
  -- ### Tail

  indexed-set-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSet C
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSet (ChainCategory.tail C x)
  indexed-set-tail C' x
    = IndexedDependentSet.indexed-set
      (indexed-set-unpack C') x

  -- ### Partial

  data IndexedPartialFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → IndexedSet C
    → IndexedSet C
    → Set
    where
  
    empty
      : {C : ChainCategory zero}
      → {C' D' : IndexedSet C}
      → PartialFunction
        (indexed-set₀ C')
        (indexed-set₀ D')
      → IndexedPartialFunction C' D'
  
    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' D' : IndexedSet C}
      → ((x : Category.Object (ChainCategory.head C))
        → IndexedPartialFunction
          (indexed-set-tail C' x)
          (indexed-set-tail D' x))
      → IndexedPartialFunction C' D'

  indexed-partial-function₀
    : {C : ChainCategory zero}
    → {C' D' : IndexedSet C}
    → IndexedPartialFunction C' D'
    → PartialFunction
      (indexed-set₀ C')
      (indexed-set₀ D')
  indexed-partial-function₀ (empty f)
    = f

  indexed-partial-function-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : IndexedSet C}
    → IndexedPartialFunction C' D'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedPartialFunction
      (indexed-set-tail C' x)
      (indexed-set-tail D' x)
  indexed-partial-function-tail (sigma F)
    = F

  indexed-partial-function-compose
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' D' E' : IndexedSet C}
    → IndexedPartialFunction D' E'
    → IndexedPartialFunction C' D'
    → IndexedPartialFunction C' E'
  indexed-partial-function-compose {n = zero} F G
    = empty
      (partial-function-compose
        (indexed-partial-function₀ F)
        (indexed-partial-function₀ G))
  indexed-partial-function-compose {n = suc _} F G
    = sigma
      (λ x → indexed-partial-function-compose
        (indexed-partial-function-tail F x)
        (indexed-partial-function-tail G x))

-- ## Modules

open Internal public
  using (IndexedDependentSet; IndexedDependentFunction;
    IndexedDependentFunctionCompose; IndexedDependentFunctionIdentity;
    IndexedDependentFunctionSquare; indexed-dependent-set;
    indexed-dependent-function; indexed-dependent-function-compose;
    indexed-dependent-function-identity; indexed-dependent-function-square)

-- ### IndexedSet

IndexedSet
  : {n : ℕ}
  → ChainCategory n
  → Set₁
IndexedSet
  = Internal.IndexedSet

open Internal.IndexedSet public

open Internal public
  using (indexed-set₀)

module IndexedSet where

  open Internal.IndexedSet public

  open Internal public using () renaming
    ( indexed-set-tail
      to tail
    ; indexed-set-unpack
      to unpack
    )

-- ### IndexedFunction

IndexedFunction
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → IndexedSet C₁
  → IndexedSet C₂
  → ChainFunctor C₁ C₂
  → Set
IndexedFunction
  = Internal.IndexedFunction

open Internal.IndexedFunction public

open Internal public
  using (indexed-function₀)

module IndexedFunction where

  open Internal.IndexedFunction public

  open Internal public using () renaming
    ( indexed-function-unpack
      to unpack
    )

-- ### IndexedFunctionIdentity

IndexedFunctionIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : IndexedSet C₁}
  → {C₂' : IndexedSet C₂}
  → {F : ChainFunctor C₁ C₂}
  → IndexedFunction C₁' C₂' F
  → Set
IndexedFunctionIdentity
  = Internal.IndexedFunctionIdentity

open Internal.IndexedFunctionIdentity public

open Internal public
  using (indexed-function-identity₀)

module IndexedFunctionIdentity where

  open Internal.IndexedFunctionIdentity public

  open Internal public using () renaming
    ( indexed-function-identity-unpack
      to unpack
    )

-- ### IndexedFunctionCompose

IndexedFunctionCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → {C' : IndexedSet C}
  → {D' : IndexedSet D}
  → {E₁' : IndexedSet E₁}
  → {E₂' : IndexedSet E₂}
  → {F : ChainFunctor D E₁}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E₂}
  → IndexedFunction D' E₁' F
  → IndexedFunction C' D' G
  → IndexedFunction C' E₂' H
  → Set
IndexedFunctionCompose
  = Internal.IndexedFunctionCompose

open Internal.IndexedFunctionCompose public

open Internal public
  using (indexed-function-compose₀)

module IndexedFunctionCompose where

  open Internal.IndexedFunctionCompose public

  open Internal public using () renaming
    ( indexed-function-compose-unpack
      to unpack
    )

-- ### IndexedFunctionSquare

IndexedFunctionSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
  → {C₁' : IndexedSet C₁}
  → {C₂' : IndexedSet C₂}
  → {D₁' : IndexedSet D₁}
  → {D₂' : IndexedSet D₂}
  → {D₃' : IndexedSet D₃}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₃}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → (F' : IndexedFunction C₁' C₂' F)
  → (G' : IndexedFunction D₁' D₃' G)
  → (H₁' : IndexedFunction C₁' D₁' H₁)
  → (H₂' : IndexedFunction C₂' D₂' H₂)
  → Set
IndexedFunctionSquare
  = Internal.IndexedFunctionSquare

open Internal.IndexedFunctionSquare public

open Internal public
  using (indexed-function-square₀)

module IndexedFunctionSquare where

  open Internal.IndexedFunctionSquare public

  open Internal public using () renaming
    ( indexed-function-square-unpack
      to unpack
    )

-- ### IndexedPartialFunction

IndexedPartialFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSet C
  → IndexedSet C
  → Set
IndexedPartialFunction
  = Internal.IndexedPartialFunction

open Internal.IndexedPartialFunction public

open Internal public
  using (indexed-partial-function₀; indexed-partial-function-compose)

module IndexedPartialFunction where

  open Internal.IndexedPartialFunction public

  open Internal public using () renaming
    ( indexed-partial-function-tail
      to tail
    )

