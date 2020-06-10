module Prover.Category.Chain where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types
  
  -- #### ChainCategory
  
  data ChainCategory
    : ℕ
    → Set₁
    
  -- #### ChainFunctor
  
  data ChainFunctor
    : {n : ℕ}
    → ChainCategory n
    → ChainCategory n
    → Set
    
  -- #### ChainFunctorIdentity
  
  data ChainFunctorIdentity
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory n}
    → ChainFunctor C₁ C₂
    → Set
    
  -- #### ChainFunctorCompose
  
  data ChainFunctorCompose
    : {n : ℕ}
    → {C D E₁ E₂ : ChainCategory n}
    → ChainFunctor D E₁
    → ChainFunctor C D
    → ChainFunctor C E₂
    → Set
    
  -- #### ChainFunctorSquare
  
  data ChainFunctorSquare
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n} 
    → ChainFunctor C₁ C₂
    → ChainFunctor D₁ D₃
    → ChainFunctor C₁ D₁
    → ChainFunctor C₂ D₂
    → Set
  
  -- #### ChainDependentCategory
  
  record ChainDependentCategory
    (C : Category)
    (n : ℕ)
    : Set₁
    
  -- #### ChainDependentFunctor
  
  record ChainDependentFunctor
    {n : ℕ}
    {C D : Category}
    (C' : ChainDependentCategory C n)
    (D' : ChainDependentCategory D n)
    : Set
    
  -- #### ChainDependentFunctorIdentity
  
  record ChainDependentFunctorIdentity
    {n : ℕ}
    {C : Category}
    {C' : ChainDependentCategory C n}
    (F : ChainDependentFunctor C' C')
    : Set
    
  -- #### ChainDependentFunctorCompose
  
  record ChainDependentFunctorCompose
    {n : ℕ}
    {C D E : Category}
    {C' : ChainDependentCategory C n}
    {D' : ChainDependentCategory D n}
    {E' : ChainDependentCategory E n}
    (F : ChainDependentFunctor D' E')
    (G : ChainDependentFunctor C' D')
    (H : ChainDependentFunctor C' E')
    : Set
    
  -- #### ChainDependentFunctorSquare
  
  record ChainDependentFunctorSquare
    {n : ℕ}
    {C₁ C₂ D₁ D₂ : Category}
    {C₁' : ChainDependentCategory C₁ n}
    {C₂' : ChainDependentCategory C₂ n}
    {D₁' : ChainDependentCategory D₁ n}
    {D₂' : ChainDependentCategory D₂ n}
    (F : ChainDependentFunctor C₁' C₂')
    (G : ChainDependentFunctor D₁' D₂')
    (H₁ : ChainDependentFunctor C₁' D₁')
    (H₂ : ChainDependentFunctor C₂' D₂')
    : Set
    
  -- ### Interface
  
  -- #### ChainCategory
  
  chain-category-head
    : {n : ℕ}
    → ChainCategory (suc n)
    → Category
  
  chain-category-unpack
    : {n : ℕ}
    → (C : ChainCategory (suc n))
    → ChainDependentCategory
      (chain-category-head C) n
  
  -- #### ChainFunctor
  
  chain-functor-unpack
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → ChainFunctor C D
    → ChainDependentFunctor
      (chain-category-unpack C)
      (chain-category-unpack D)
  
  -- ### Definitions
  
  -- #### ChainCategory
  
  data ChainCategory where
  
    empty
      : ChainCategory zero

    sigma
      : {n : ℕ}
      → {C : Category}
      → ChainDependentCategory C n
      → ChainCategory (suc n)
  
  chain-category-head (sigma {C = C} _)
    = C
  
  chain-category-unpack (sigma C')
    = C'
  
  -- #### ChainFunctor
  
  data ChainFunctor where
  
    empty
      : {C D : ChainCategory zero}
      → ChainFunctor C D

    sigma
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → ChainDependentFunctor
        (chain-category-unpack C)
        (chain-category-unpack D)
      → ChainFunctor C D
  
  chain-functor-unpack (sigma F)
    = F
  
  -- #### ChainFunctorIdentity
  
  data ChainFunctorIdentity where
  
    empty
      : {C : ChainCategory zero}
      → {F : ChainFunctor C C}
      → ChainFunctorIdentity F

    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {F : ChainFunctor C C}
      → ChainDependentFunctorIdentity
        (chain-functor-unpack F)
      → ChainFunctorIdentity F
  
  -- #### ChainFunctorCompose
  
  data ChainFunctorCompose where
  
    empty
      : {C D E : ChainCategory zero}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → ChainFunctorCompose F G H

    sigma
      : {n : ℕ}
      → {C D E : ChainCategory (suc n)}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → ChainDependentFunctorCompose
        (chain-functor-unpack F)
        (chain-functor-unpack G)
        (chain-functor-unpack H)
      → ChainFunctorCompose F G H
  
  -- #### ChainFunctorSquare
  
  data ChainFunctorSquare where
  
    empty
      : {C₁ C₂ D₁ D₂ : ChainCategory zero}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → ChainFunctorSquare F G H₁ H₂
    
    sigma
      : {n : ℕ}
      → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → ChainDependentFunctorSquare
        (chain-functor-unpack F)
        (chain-functor-unpack G)
        (chain-functor-unpack H₁)
        (chain-functor-unpack H₂)
      → ChainFunctorSquare F G H₁ H₂
  
  -- #### ChainDependentCategory
  
  record ChainDependentCategory C n where

    inductive

    no-eta-equality

    constructor
      
      chain-dependent-category

    field

      chain-category
        : Category.Object C
        → ChainCategory n
  
      chain-functor
        : {x y : Category.Object C}
        → Category.Arrow C x y
        → ChainFunctor
          (chain-category x)
          (chain-category y)

      chain-functor-identity
        : (x : Category.Object C)
        → ChainFunctorIdentity
          (chain-functor (Category.identity C x))

      chain-functor-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → ChainFunctorCompose
          (chain-functor f)
          (chain-functor g)
          (chain-functor (Category.compose C f g))
  
  -- #### ChainDependentFunctor
  
  record ChainDependentFunctor {_ C D} C' D' where

    inductive

    no-eta-equality

    constructor

      chain-dependent-functor

    field

      functor
        : Functor C D
  
    open Functor functor public
  
    field

      chain-functor
        : (x : Category.Object C)
        → ChainFunctor
          (ChainDependentCategory.chain-category C' x)
          (ChainDependentCategory.chain-category D' (base x))
  
      chain-functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → ChainFunctorSquare
          (ChainDependentCategory.chain-functor C' f)
          (ChainDependentCategory.chain-functor D' (map f))
          (chain-functor x)
          (chain-functor y)
    
  -- #### ChainDependentFunctorIdentity
  
  record ChainDependentFunctorIdentity {_ C} F where

    inductive

    constructor

      chain-dependent-functor-identity

    field

      functor
        : FunctorIdentity
          (ChainDependentFunctor.functor F)
  
    open FunctorIdentity functor public
  
    field

      chain-functor
        : (x : Category.Object C)
        → ChainFunctorIdentity
          (ChainDependentFunctor.chain-functor F x)
  
  -- #### ChainDependentFunctorCompose
  
  record ChainDependentFunctorCompose {_ C} F G H where

    inductive

    constructor

      chain-dependent-functor-compose

    field

      functor
        : FunctorCompose
          (ChainDependentFunctor.functor F)
          (ChainDependentFunctor.functor G)
          (ChainDependentFunctor.functor H)

    open FunctorCompose functor public
  
    field

      chain-functor
        : (x : Category.Object C)
        → ChainFunctorCompose
          (ChainDependentFunctor.chain-functor F
            (ChainDependentFunctor.base G x))
          (ChainDependentFunctor.chain-functor G x)
          (ChainDependentFunctor.chain-functor H x)
  
  -- #### ChainDependentFunctorSquare
  
  record ChainDependentFunctorSquare {_ C₁} F G H₁ H₂ where

    inductive

    constructor

      chain-dependent-functor-square

    field

      functor
        : FunctorSquare
          (ChainDependentFunctor.functor F)
          (ChainDependentFunctor.functor G)
          (ChainDependentFunctor.functor H₁)
          (ChainDependentFunctor.functor H₂)

    open FunctorSquare functor public
  
    field
  
      chain-functor
        : (x₁ : Category.Object C₁)
        → ChainFunctorSquare
          (ChainDependentFunctor.chain-functor F x₁)
          (ChainDependentFunctor.chain-functor G
            (ChainDependentFunctor.base H₁ x₁))
          (ChainDependentFunctor.chain-functor H₁ x₁)
          (ChainDependentFunctor.chain-functor H₂
            (ChainDependentFunctor.base F x₁))

  -- ### Construction

  -- #### ChainDependentCategory
  
  module ChainDependentCategory₀
    (C : Category)
    where

    chain-category
      : Category.Object C
      → ChainCategory zero
    chain-category _
      = empty

    chain-functor
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → ChainFunctor
        (chain-category x)
        (chain-category y)
    chain-functor _
      = empty

    chain-functor-identity
      : (x : Category.Object C)
      → ChainFunctorIdentity
        (chain-functor (Category.identity C x))
    chain-functor-identity _
      = empty

    chain-functor-compose
      : {x y z : Category.Object C}
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → ChainFunctorCompose
        (chain-functor f)
        (chain-functor g)
        (chain-functor (Category.compose C f g))
    chain-functor-compose _ _
      = empty
  
  chain-dependent-category₀
    : (C : Category)
    → ChainDependentCategory C zero
  chain-dependent-category₀ C
    = record {ChainDependentCategory₀ C}
  
  -- #### ChainDependentFunctor
  
  module _
    {C D : Category}
    where

    module ChainDependentFunctor₀
      (F : Functor C D)
      where

      functor
        : Functor C D
      functor
        = F
  
      open Functor functor

      chain-functor
        : (x : Category.Object C)
        → ChainFunctor
          (ChainDependentCategory.chain-category
            (chain-dependent-category₀ C) x)
          (ChainDependentCategory.chain-category
            (chain-dependent-category₀ D) (base x))
      chain-functor _
        = empty
  
      chain-functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → ChainFunctorSquare
          (ChainDependentCategory.chain-functor
            (chain-dependent-category₀ C) f)
          (ChainDependentCategory.chain-functor
            (chain-dependent-category₀ D) (map f))
          (chain-functor x)
          (chain-functor y)
      chain-functor-square _
        = empty
    
    chain-dependent-functor₀
      : Functor C D
      → ChainDependentFunctor
        (chain-dependent-category₀ C)
        (chain-dependent-category₀ D)
    chain-dependent-functor₀ F
      = record {ChainDependentFunctor₀ F}
  
  -- chain-transformation₀ F
  --   = chain-transformation F
  --     (λ _ → empty)
  --     (λ _ → empty)
  
  -- #### ChainDependentFunctorIdentity
  
  module _
    {C : Category}
    {F : Functor C C}
    where

    module ChainDependentFunctorIdentity₀
      (p : FunctorIdentity F)
      where

      functor
        : FunctorIdentity
          (ChainDependentFunctor.functor (chain-dependent-functor₀ F))
      functor
        = p
  
      chain-functor
        : (x : Category.Object C)
        → ChainFunctorIdentity
          (ChainDependentFunctor.chain-functor (chain-dependent-functor₀ F) x)
      chain-functor _
        = empty
  
    chain-dependent-functor-identity₀
      : FunctorIdentity F
      → ChainDependentFunctorIdentity
        (chain-dependent-functor₀ F)
    chain-dependent-functor-identity₀ p
      = record {ChainDependentFunctorIdentity₀ p}
  
  -- #### ChainDependentFunctorCompose
  
  module _
    {C D E : Category}
    {F : Functor D E}
    {G : Functor C D}
    {H : Functor C E}
    where

    module ChainDependentFunctorCompose₀
      (p : FunctorCompose F G H)
      where

      functor
        : FunctorCompose
          (ChainDependentFunctor.functor (chain-dependent-functor₀ F))
          (ChainDependentFunctor.functor (chain-dependent-functor₀ G))
          (ChainDependentFunctor.functor (chain-dependent-functor₀ H))
      functor
        = p

      chain-functor
        : (x : Category.Object C)
        → ChainFunctorCompose
          (ChainDependentFunctor.chain-functor (chain-dependent-functor₀ F)
            (ChainDependentFunctor.base (chain-dependent-functor₀ G) x))
          (ChainDependentFunctor.chain-functor (chain-dependent-functor₀ G) x)
          (ChainDependentFunctor.chain-functor (chain-dependent-functor₀ H) x)
      chain-functor _
        = empty
  
    chain-dependent-functor-compose₀
      : FunctorCompose F G H
      → ChainDependentFunctorCompose
        (chain-dependent-functor₀ F)
        (chain-dependent-functor₀ G)
        (chain-dependent-functor₀ H)
    chain-dependent-functor-compose₀ p
      = record {ChainDependentFunctorCompose₀ p}

  -- #### ChainDependentFunctorSquare
  
  module _
    {C₁ C₂ D₁ D₂ : Category}
    {F : Functor C₁ C₂}
    {G : Functor D₁ D₂}
    {H₁ : Functor C₁ D₁}
    {H₂ : Functor C₂ D₂}
    where

    module ChainDependentFunctorSquare₀
      (s : FunctorSquare F G H₁ H₂) 
      where

      functor
        : FunctorSquare
          (ChainDependentFunctor.functor (chain-dependent-functor₀ F))
          (ChainDependentFunctor.functor (chain-dependent-functor₀ G))
          (ChainDependentFunctor.functor (chain-dependent-functor₀ H₁))
          (ChainDependentFunctor.functor (chain-dependent-functor₀ H₂))
      functor
        = s

      chain-functor
        : (x₁ : Category.Object C₁)
        → ChainFunctorSquare
          (ChainDependentFunctor.chain-functor (chain-dependent-functor₀ F) x₁)
          (ChainDependentFunctor.chain-functor (chain-dependent-functor₀ G)
            (ChainDependentFunctor.base (chain-dependent-functor₀ H₁) x₁))
          (ChainDependentFunctor.chain-functor (chain-dependent-functor₀ H₁) x₁)
          (ChainDependentFunctor.chain-functor (chain-dependent-functor₀ H₂)
            (ChainDependentFunctor.base (chain-dependent-functor₀ F) x₁))
      chain-functor _
        = empty

    chain-dependent-functor-square₀
      : FunctorSquare F G H₁ H₂ 
      → ChainDependentFunctorSquare
        (chain-dependent-functor₀ F)
        (chain-dependent-functor₀ G)
        (chain-dependent-functor₀ H₁)
        (chain-dependent-functor₀ H₂)
    chain-dependent-functor-square₀ s
      = record {ChainDependentFunctorSquare₀ s}

  -- ### Tail

  chain-category-tail
    : {n : ℕ}
    → (C : ChainCategory (suc n))
    → Category.Object (chain-category-head C)
    → ChainCategory n
  chain-category-tail C
    = ChainDependentCategory.chain-category
      (chain-category-unpack C)

-- ## Modules

open Internal public
  using (ChainDependentCategory; ChainDependentFunctor;
    ChainDependentFunctorCompose; ChainDependentFunctorIdentity;
    ChainDependentFunctorSquare; chain-dependent-category;
    chain-dependent-category₀; chain-dependent-functor;
    chain-dependent-functor₀; chain-dependent-functor-compose;
    chain-dependent-functor-compose₀; chain-dependent-functor-identity;
    chain-dependent-functor-identity₀; chain-dependent-functor-square;
    chain-dependent-functor-square₀)

-- ### ChainCategory

ChainCategory
  : ℕ
  → Set₁
ChainCategory
  = Internal.ChainCategory
  
open Internal.ChainCategory public

module ChainCategory where

  open Internal.ChainCategory public

  open Internal public using () renaming
    ( chain-category-head
      to head
    ; chain-category-tail
      to tail
    ; chain-category-unpack
      to unpack
    )

-- ### ChainFunctor

ChainFunctor
  : {n : ℕ}
  → ChainCategory n
  → ChainCategory n
  → Set
ChainFunctor
  = Internal.ChainFunctor
  
open Internal.ChainFunctor public

module ChainFunctor where
  
  open Internal.ChainFunctor public

  open Internal public using () renaming
    ( chain-functor-unpack
      to unpack
    )

-- ### ChainFunctorIdentity

ChainFunctorIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → ChainFunctor C₁ C₂
  → Set
ChainFunctorIdentity
  = Internal.ChainFunctorIdentity
  
open Internal.ChainFunctorIdentity public

module ChainFunctorIdentity where
  
  open Internal.ChainFunctorIdentity public

-- ### ChainFunctorCompose

ChainFunctorCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → ChainFunctor D E₁
  → ChainFunctor C D
  → ChainFunctor C E₂
  → Set
ChainFunctorCompose
  = Internal.ChainFunctorCompose
  
open Internal.ChainFunctorCompose public

module ChainFunctorCompose where

  open Internal.ChainFunctorCompose public

-- ### ChainFunctorSquare

ChainFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n} 
  → ChainFunctor C₁ C₂
  → ChainFunctor D₁ D₃
  → ChainFunctor C₁ D₁
  → ChainFunctor C₂ D₂
  → Set
ChainFunctorSquare
  = Internal.ChainFunctorSquare

open Internal.ChainFunctorSquare public

module ChainFunctorSquare where

  open Internal.ChainFunctorSquare public

