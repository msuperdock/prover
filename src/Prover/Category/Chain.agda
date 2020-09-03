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
  
  -- ### Interface

  -- #### ChainCategory

  chain-category-head
    : {n : ℕ}
    → ChainCategory (suc n)
    → Category

  chain-category-object
    : {n : ℕ}
    → ChainCategory (suc n)
    → Set

  chain-category-arrow
    : {n : ℕ}
    → (C : ChainCategory (suc n))
    → chain-category-object C
    → chain-category-object C
    → Set

  chain-category-identity
    : {n : ℕ}
    → (C : ChainCategory (suc n))
    → (x : chain-category-object C)
    → chain-category-arrow C x x

  chain-category-compose
    : {n : ℕ}
    → (C : ChainCategory (suc n))
    → {x y z : chain-category-object C}
    → chain-category-arrow C y z
    → chain-category-arrow C x y
    → chain-category-arrow C x z

  chain-category-tail
    : {n : ℕ}
    → (C : ChainCategory (suc n))
    → chain-category-object C
    → ChainCategory n

  chain-category-chain-functor
    : {n : ℕ}
    → (C : ChainCategory (suc n))
    → {x y : chain-category-object C}
    → chain-category-arrow C x y
    → ChainFunctor
      (chain-category-tail C x)
      (chain-category-tail C y)

  -- #### ChainFunctor

  chain-functor-head
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → ChainFunctor C D
    → Functor
      (chain-category-head C)
      (chain-category-head D)

  chain-functor-base
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → ChainFunctor C D
    → chain-category-object C
    → chain-category-object D

  chain-functor-map
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → (F : ChainFunctor C D)
    → {x y : chain-category-object C}
    → chain-category-arrow C x y
    → chain-category-arrow D (chain-functor-base F x) (chain-functor-base F y)

  chain-functor-tail
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → (F : ChainFunctor C D)
    → (x : chain-category-object C)
    → ChainFunctor
      (chain-category-tail C x)
      (chain-category-tail D (chain-functor-base F x))

  -- ### Definitions
  
  -- #### ChainCategory
  
  data ChainCategory where
  
    nil
      : ChainCategory zero

    cons
      : {n : ℕ}
      → (C : Category)
      → (C' : Category.Object C
        → ChainCategory n)
      → (F : {x y : Category.Object C}
        → Category.Arrow C x y
        → ChainFunctor (C' x) (C' y))
      → ((x : Category.Object C)
        → ChainFunctorIdentity (F (Category.identity C x)))
      → ({x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → ChainFunctorCompose (F f) (F g) (F (Category.compose C f g)))
      → ChainCategory (suc n)
  
  chain-category-head (cons C _ _ _ _)
    = C

  chain-category-object C
    = Category.Object
      (chain-category-head C)

  chain-category-arrow C
    = Category.Arrow
      (chain-category-head C)

  chain-category-identity C
    = Category.identity
      (chain-category-head C)

  chain-category-compose C
    = Category.compose
      (chain-category-head C)

  chain-category-tail (cons _ C' _ _ _)
    = C'

  chain-category-chain-functor (cons _ _ F _ _)
    = F

  -- #### ChainFunctor
  
  data ChainFunctor where
  
    nil
      : {C D : ChainCategory zero}
      → ChainFunctor C D

    cons
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → (F : Functor
          (chain-category-head C)
          (chain-category-head D))
      → (F' : (x : chain-category-object C)
        → ChainFunctor
          (chain-category-tail C x)
          (chain-category-tail D (Functor.base F x)))
      → ({x y : chain-category-object C}
        → (f : Category.Arrow (chain-category-head C) x y)
        → ChainFunctorSquare
          (chain-category-chain-functor C f)
          (chain-category-chain-functor D (Functor.map F f))
          (F' x)
          (F' y))
      → ChainFunctor C D
  
  chain-functor-head (cons F _ _)
    = F

  chain-functor-base F
    = Functor.base
      (chain-functor-head F)

  chain-functor-map F
    = Functor.map
      (chain-functor-head F)

  chain-functor-tail (cons _ F' _)
    = F'
  
  -- #### ChainFunctorIdentity
  
  data ChainFunctorIdentity where
  
    nil
      : {C : ChainCategory zero}
      → {F : ChainFunctor C C}
      → ChainFunctorIdentity F

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {F : ChainFunctor C C}
      → FunctorIdentity
        (chain-functor-head F)
      → ((x : chain-category-object C)
        → ChainFunctorIdentity
          (chain-functor-tail F x))
      → ChainFunctorIdentity F
  
  -- #### ChainFunctorCompose
  
  data ChainFunctorCompose where
  
    nil
      : {C D E : ChainCategory zero}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → ChainFunctorCompose F G H

    cons
      : {n : ℕ}
      → {C D E : ChainCategory (suc n)}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → FunctorCompose
        (chain-functor-head F)
        (chain-functor-head G)
        (chain-functor-head H)
      → ((x : chain-category-object C)
        → ChainFunctorCompose
          (chain-functor-tail F (chain-functor-base G x))
          (chain-functor-tail G x)
          (chain-functor-tail H x))
      → ChainFunctorCompose F G H
  
  -- #### ChainFunctorSquare
  
  data ChainFunctorSquare where
  
    nil
      : {C₁ C₂ D₁ D₂ : ChainCategory zero}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → ChainFunctorSquare F G H₁ H₂
    
    cons
      : {n : ℕ}
      → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → FunctorSquare
        (chain-functor-head F)
        (chain-functor-head G)
        (chain-functor-head H₁)
        (chain-functor-head H₂)
      → ((x₁ : chain-category-object C₁)
        → ChainFunctorSquare
          (chain-functor-tail F x₁)
          (chain-functor-tail G (chain-functor-base H₁ x₁))
          (chain-functor-tail H₁ x₁)
          (chain-functor-tail H₂ (chain-functor-base F x₁)))
      → ChainFunctorSquare F G H₁ H₂
  
  -- ### Construction

  -- #### ChainCategory

  chain-category₁
    : Category
    → ChainCategory (suc zero)
  chain-category₁ C
    = cons C
      (λ _ → nil)
      (λ _ → nil)
      (λ _ → nil)
      (λ _ _ → nil)

  -- #### ChainFunctor

  chain-functor₁
    : {C D : Category}
    → Functor C D
    → ChainFunctor
      (chain-category₁ C)
      (chain-category₁ D)
  chain-functor₁ F
    = cons F
      (λ _ → nil)
      (λ _ → nil)

  -- #### ChainFunctorIdentity

  chain-functor-identity₁
    : {C : Category}
    → {F : Functor C C}
    → FunctorIdentity F
    → ChainFunctorIdentity
      (chain-functor₁ F)
  chain-functor-identity₁ p
    = cons p
      (λ _ → nil)

  -- #### ChainFunctorCompose

  chain-functor-compose₁
    : {C D E : Category}
    → {F : Functor D E}
    → {G : Functor C D}
    → {H : Functor C E}
    → FunctorCompose F G H
    → ChainFunctorCompose
      (chain-functor₁ F)
      (chain-functor₁ G)
      (chain-functor₁ H)
  chain-functor-compose₁ p
    = cons p
      (λ _ → nil)

  -- #### ChainFunctorSquare

  chain-functor-square₁
    : {C₁ C₂ D₁ D₂ : Category}
    → {F : Functor C₁ C₂}
    → {G : Functor D₁ D₂}
    → {H₁ : Functor C₁ D₁}
    → {H₂ : Functor C₂ D₂}
    → FunctorSquare F G H₁ H₂
    → ChainFunctorSquare
      (chain-functor₁ F)
      (chain-functor₁ G)
      (chain-functor₁ H₁)
      (chain-functor₁ H₂)
  chain-functor-square₁ s
    = cons s
      (λ _ → nil)

-- ## Modules

open Internal public
  using (ChainFunctorCompose; ChainFunctorIdentity; ChainFunctorSquare;
    chain-functor-compose₁; chain-functor-identity₁; chain-functor-square₁)

open ChainFunctorCompose public
open ChainFunctorIdentity public
open ChainFunctorSquare public

-- ### ChainCategory

ChainCategory
  : ℕ
  → Set₁
ChainCategory
  = Internal.ChainCategory
  
open Internal.ChainCategory public

open Internal public
  using (chain-category₁)

module ChainCategory where

  open Internal public using () renaming
    ( chain-category-arrow
      to Arrow
    ; chain-category-object
      to Object
    ; chain-category-chain-functor
      to chain-functor
    ; chain-category-compose
      to compose
    ; chain-category-head
      to head
    ; chain-category-identity
      to identity
    ; chain-category-tail
      to tail
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

open Internal public
  using (chain-functor₁)

module ChainFunctor where
  
  open Internal public using () renaming
    ( chain-functor-base
      to base
    ; chain-functor-head
      to head
    ; chain-functor-map
      to map
    ; chain-functor-tail
      to tail
    )

