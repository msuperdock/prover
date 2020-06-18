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

  indexed-set₀
    : {C : ChainCategory zero}
    → IndexedSimpleCategory C
    → Set
  
  indexed-set-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSimpleCategory C
    → IndexedSimpleDependentCategory
      (ChainCategory.unpack C)

  -- #### IndexedSimpleFunctor

  indexed-function₀
    : {C D : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {F : ChainFunctor C D}
    → IndexedSimpleFunctor C' D' F
    → Function
      (indexed-set₀ C')
      (indexed-set₀ D')

  indexed-function-unpack
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {F : ChainFunctor C D}
    → IndexedSimpleFunctor C' D' F
    → IndexedSimpleDependentFunctor
      (indexed-set-unpack C')
      (indexed-set-unpack D')
      (ChainFunctor.unpack F)

  -- #### IndexedSimpleFunctorIdentity

  indexed-function-identity₀
    : {C : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedSimpleFunctor C' C' F}
    → IndexedSimpleFunctorIdentity F'
    → FunctionIdentity
      (indexed-function₀ F')

  indexed-function-identity-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedSimpleFunctor C' C' F}
    → IndexedSimpleFunctorIdentity F'
    → IndexedSimpleDependentFunctorIdentity
      (indexed-function-unpack F')

  -- #### IndexedSimpleFunctorCompose

  indexed-function-compose₀
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
      (indexed-function₀ F')
      (indexed-function₀ G')
      (indexed-function₀ H')

  indexed-function-compose-unpack
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
      (indexed-function-unpack F')
      (indexed-function-unpack G')
      (indexed-function-unpack H')

  -- #### IndexedSimpleFunctorSquare

  indexed-function-square₀
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
      (indexed-function₀ F')
      (indexed-function₀ G')
      (indexed-function₀ H₁')
      (indexed-function₀ H₂')

  indexed-function-square-unpack
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
      (indexed-function-unpack F')
      (indexed-function-unpack G')
      (indexed-function-unpack H₁')
      (indexed-function-unpack H₂')

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
  
  indexed-set₀ (empty A)
    = A

  indexed-set-unpack (sigma A)
    = A

  -- #### IndexedSimpleFunctor
  
  data IndexedSimpleFunctor where
  
    empty
      : {C D : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {F : ChainFunctor C D}
      → Function
        (indexed-set₀ C')
        (indexed-set₀ D')
      → IndexedSimpleFunctor C' D' F
  
    sigma
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {F : ChainFunctor C D}
      → IndexedSimpleDependentFunctor
        (indexed-set-unpack C')
        (indexed-set-unpack D')
        (ChainFunctor.unpack F)
      → IndexedSimpleFunctor C' D' F
  
  indexed-function₀ (empty f)
    = f

  indexed-function-unpack (sigma f)
    = f

  -- #### IndexedSimpleFunctorIdentity
  
  data IndexedSimpleFunctorIdentity where
  
    empty
      : {C : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedSimpleFunctor C' C' F}
      → FunctionIdentity
        (indexed-function₀ F')
      → IndexedSimpleFunctorIdentity F'
  
    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedSimpleFunctor C' C' F}
      → IndexedSimpleDependentFunctorIdentity
        (indexed-function-unpack F')
      → IndexedSimpleFunctorIdentity F'
  
  indexed-function-identity₀ (empty p)
    = p

  indexed-function-identity-unpack (sigma p)
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
        (indexed-function₀ F')
        (indexed-function₀ G')
        (indexed-function₀ H')
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
        (indexed-function-unpack F')
        (indexed-function-unpack G')
        (indexed-function-unpack H')
      → IndexedSimpleFunctorCompose F' G' H'
  
  indexed-function-compose₀ (empty p)
    = p

  indexed-function-compose-unpack (sigma p)
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
        (indexed-function₀ F')
        (indexed-function₀ G')
        (indexed-function₀ H₁')
        (indexed-function₀ H₂')
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
        (indexed-function-unpack F')
        (indexed-function-unpack G')
        (indexed-function-unpack H₁')
        (indexed-function-unpack H₂')
      → IndexedSimpleFunctorSquare F' G' H₁' H₂'
  
  indexed-function-square₀ (empty s)
    = s

  indexed-function-square-unpack (sigma s)
    = s

  -- #### IndexedSimpleDependentCategory
  
  record IndexedSimpleDependentCategory {_ C} C' where
  
    inductive
  
    no-eta-equality
  
    constructor

      indexed-dependent-set

    field
  
      indexed-set
        : (x : Category.Object C)
        → IndexedSimpleCategory
          (ChainDependentCategory.chain-category C' x)
  
      indexed-function
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → IndexedSimpleFunctor
          (indexed-set x)
          (indexed-set y)
          (ChainDependentCategory.chain-functor C' f)
  
      indexed-function-identity
        : (x : Category.Object C)
        → IndexedSimpleFunctorIdentity
          (indexed-function (Category.identity C x))
  
      indexed-function-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → IndexedSimpleFunctorCompose
          (indexed-function f)
          (indexed-function g)
          (indexed-function (Category.compose C f g))
  
  -- #### IndexedSimpleDependentFunctor
  
  record IndexedSimpleDependentFunctor
    {_ C} C'' D'' F
    where

    inductive

    no-eta-equality

    constructor
    
      indexed-dependent-function

    field

      indexed-function
        : (x : Category.Object C)
        → IndexedSimpleFunctor
          (IndexedSimpleDependentCategory.indexed-set C'' x)
          (IndexedSimpleDependentCategory.indexed-set D''
            (ChainDependentFunctor.base F x))
          (ChainDependentFunctor.chain-functor F x)

      indexed-function-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → IndexedSimpleFunctorSquare
          (IndexedSimpleDependentCategory.indexed-function C'' f)
          (IndexedSimpleDependentCategory.indexed-function D''
            (ChainDependentFunctor.map F f))
          (indexed-function x)
          (indexed-function y)

  -- #### IndexedSimpleDependentFunctorIdentity
  
  record IndexedSimpleDependentFunctorIdentity
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
        → IndexedSimpleFunctorIdentity
          (IndexedSimpleDependentFunctor.indexed-function F' x)

  -- #### IndexedSimpleDependentFunctorCompose
  
  record IndexedSimpleDependentFunctorCompose
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
        → IndexedSimpleFunctorCompose
          (IndexedSimpleDependentFunctor.indexed-function F'
            (ChainDependentFunctor.base G x))
          (IndexedSimpleDependentFunctor.indexed-function G' x)
          (IndexedSimpleDependentFunctor.indexed-function H' x)
  
  -- #### IndexedSimpleDependentFunctorSquare
  
  record IndexedSimpleDependentFunctorSquare
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
        → IndexedSimpleFunctorSquare
          (IndexedSimpleDependentFunctor.indexed-function F' x₁)
          (IndexedSimpleDependentFunctor.indexed-function G'
            (ChainDependentFunctor.base H₁ x₁))
          (IndexedSimpleDependentFunctor.indexed-function H₁' x₁)
          (IndexedSimpleDependentFunctor.indexed-function H₂'
            (ChainDependentFunctor.base F x₁))
  
  -- ### Tail

  indexed-set-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSimpleCategory C
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSimpleCategory (ChainCategory.tail C x)
  indexed-set-tail C' x
    = IndexedSimpleDependentCategory.indexed-set
      (indexed-set-unpack C') x

  -- ### Partial

  data IndexedPartialFunction
    : {n : ℕ}
    → {C : ChainCategory n}
    → IndexedSimpleCategory C
    → IndexedSimpleCategory C
    → Set
    where
  
    empty
      : {C : ChainCategory zero}
      → {C' D' : IndexedSimpleCategory C}
      → PartialFunction
        (indexed-set₀ C')
        (indexed-set₀ D')
      → IndexedPartialFunction C' D'
  
    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' D' : IndexedSimpleCategory C}
      → ((x : Category.Object (ChainCategory.head C))
        → IndexedPartialFunction
          (indexed-set-tail C' x)
          (indexed-set-tail D' x))
      → IndexedPartialFunction C' D'

  indexed-partial-function₀
    : {C : ChainCategory zero}
    → {C' D' : IndexedSimpleCategory C}
    → IndexedPartialFunction C' D'
    → PartialFunction
      (indexed-set₀ C')
      (indexed-set₀ D')
  indexed-partial-function₀ (empty f)
    = f

  indexed-partial-function-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : IndexedSimpleCategory C}
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
    → {C' D' E' : IndexedSimpleCategory C}
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
  using (IndexedSimpleDependentCategory; IndexedSimpleDependentFunctor;
    IndexedSimpleDependentFunctorCompose; IndexedSimpleDependentFunctorIdentity;
    IndexedSimpleDependentFunctorSquare; indexed-dependent-set;
    indexed-dependent-function; indexed-dependent-function-compose;
    indexed-dependent-function-identity; indexed-dependent-function-square)

-- ### IndexedSimpleCategory

IndexedSimpleCategory
  : {n : ℕ}
  → ChainCategory n
  → Set₁
IndexedSimpleCategory
  = Internal.IndexedSimpleCategory

open Internal.IndexedSimpleCategory public

open Internal public
  using (indexed-set₀)

module IndexedSimpleCategory where

  open Internal.IndexedSimpleCategory public

  open Internal public using () renaming
    ( indexed-set-tail
      to tail
    ; indexed-set-unpack
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
  using (indexed-function₀)

module IndexedSimpleFunctor where

  open Internal.IndexedSimpleFunctor public

  open Internal public using () renaming
    ( indexed-function-unpack
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
  using (indexed-function-identity₀)

module IndexedSimpleFunctorIdentity where

  open Internal.IndexedSimpleFunctorIdentity public

  open Internal public using () renaming
    ( indexed-function-identity-unpack
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
  using (indexed-function-compose₀)

module IndexedSimpleFunctorCompose where

  open Internal.IndexedSimpleFunctorCompose public

  open Internal public using () renaming
    ( indexed-function-compose-unpack
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
  using (indexed-function-square₀)

module IndexedSimpleFunctorSquare where

  open Internal.IndexedSimpleFunctorSquare public

  open Internal public using () renaming
    ( indexed-function-square-unpack
      to unpack
    )

-- ### IndexedPartialFunction

IndexedPartialFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → IndexedSimpleCategory C
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

