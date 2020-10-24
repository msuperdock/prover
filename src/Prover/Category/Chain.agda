module Prover.Category.Chain where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare)
open import Prover.Prelude

-- ## Base

-- ### Chain₀Category

record Chain₀Category
  : Set₁
  where

  no-eta-equality

  constructor

    nil

-- ### Chain₀Functor

record Chain₀Functor
  (C D : Chain₀Category)
  : Set
  where

  no-eta-equality

  constructor
    
    nil

-- ### Chain₀FunctorEqual

record Chain₀FunctorEqual
  {C D₁ D₂ : Chain₀Category}
  (F₁ : Chain₀Functor C D₁)
  (F₂ : Chain₀Functor C D₂)
  : Set
  where

  constructor

    nil

-- ### Chain₀FunctorIdentity

record Chain₀FunctorIdentity
  {C₁ C₂ : Chain₀Category}
  (F : Chain₀Functor C₁ C₂)
  : Set
  where

  constructor

    nil

-- ### Chain₀FunctorCompose

record Chain₀FunctorCompose
  {C D E₁ E₂ : Chain₀Category}
  (F : Chain₀Functor D E₁)
  (G : Chain₀Functor C D)
  (H : Chain₀Functor C E₂)
  : Set
  where

  constructor

    nil

-- ### Chain₀FunctorSquare

record Chain₀FunctorSquare
  {C₁ C₂ D₁ D₂ D₃ : Chain₀Category}
  (F : Chain₀Functor C₁ C₂)
  (G : Chain₀Functor D₁ D₃)
  (H₁ : Chain₀Functor C₁ D₁)
  (H₂ : Chain₀Functor C₂ D₂)
  : Set
  where

  constructor

    nil

-- ## Types

-- ### ChainCategory

ChainCategory
  : ℕ
  → Set₁

record ChainCategory'
  (n : ℕ)
  : Set₁

-- ### ChainFunctor

ChainFunctor
  : {n : ℕ}
  → ChainCategory n
  → ChainCategory n
  → Set
  
record ChainFunctor'
  {n : ℕ}
  (C : ChainCategory (suc n))
  (D : ChainCategory (suc n))
  : Set

-- ### ChainFunctorEqual

ChainFunctorEqual
  : {n : ℕ}
  → {C D₁ D₂ : ChainCategory n}
  → ChainFunctor C D₁
  → ChainFunctor C D₂
  → Set

record ChainFunctorEqual'
  {n : ℕ}
  {C D₁ D₂ : ChainCategory (suc n)}
  (F₁ : ChainFunctor C D₁)
  (F₂ : ChainFunctor C D₂)
  : Set

-- ### ChainFunctorIdentity

ChainFunctorIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → ChainFunctor C₁ C₂
  → Set
  
record ChainFunctorIdentity'
  {n : ℕ}
  {C₁ C₂ : ChainCategory (suc n)}
  (F : ChainFunctor C₁ C₂)
  : Set
  
-- ### ChainFunctorCompose

ChainFunctorCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → ChainFunctor D E₁
  → ChainFunctor C D
  → ChainFunctor C E₂
  → Set
  
record ChainFunctorCompose'
  {n : ℕ}
  {C D E₁ E₂ : ChainCategory (suc n)}
  (F : ChainFunctor D E₁)
  (G : ChainFunctor C D)
  (H : ChainFunctor C E₂)
  : Set
  
-- ### ChainFunctorSquare

ChainFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n} 
  → ChainFunctor C₁ C₂
  → ChainFunctor D₁ D₃
  → ChainFunctor C₁ D₁
  → ChainFunctor C₂ D₂
  → Set

record ChainFunctorSquare'
  {n : ℕ}
  {C₁ C₂ D₁ D₂ D₃ : ChainCategory (suc n)} 
  (F : ChainFunctor C₁ C₂)
  (G : ChainFunctor D₁ D₃)
  (H₁ : ChainFunctor C₁ D₁)
  (H₂ : ChainFunctor C₂ D₂)
  : Set

-- ## Definitions

-- ### ChainCategory

ChainCategory zero
  = Chain₀Category
ChainCategory (suc n)
  = ChainCategory' n

record ChainCategory' n where

  inductive

  no-eta-equality

  field

    category
      : Category

  open Category category public

  field

    category'
      : Object
      → ChainCategory n

    functor
      : {x y : Object}
      → Arrow x y
      → ChainFunctor
        (category' x)
        (category' y)

    functor-equal
      : {x y : Object}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ChainFunctorEqual
        (functor f₁)
        (functor f₂)

    functor-identity
      : (x : Object)
      → ChainFunctorIdentity
        (functor (identity x))

    functor-compose
      : {x y z : Object}
      → (f : Arrow y z)
      → (g : Arrow x y)
      → ChainFunctorCompose
        (functor f)
        (functor g)
        (functor (compose f g))

module ChainCategory
  = ChainCategory'

-- ### ChainFunctor

ChainFunctor {n = zero}
  = Chain₀Functor
ChainFunctor {n = suc _}
  = ChainFunctor'

record ChainFunctor' C D where

  inductive

  no-eta-equality

  field

    functor
      : Functor
        (ChainCategory.category C)
        (ChainCategory.category D)

  open Functor functor public

  field

    functor'
      : (x : ChainCategory.Object C)
      → ChainFunctor
        (ChainCategory.category' C x)
        (ChainCategory.category' D (base x))

    functor-square
      : {x y : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C x y)
      → ChainFunctorSquare
        (ChainCategory.functor C f)
        (ChainCategory.functor D (map f))
        (functor' x)
        (functor' y)

module ChainFunctor
  = ChainFunctor'

-- ### ChainFunctorEqual

ChainFunctorEqual {n = zero}
  = Chain₀FunctorEqual
ChainFunctorEqual {n = suc _}
  = ChainFunctorEqual'

record ChainFunctorEqual' {_ C} F₁ F₂ where

  inductive

  field

    functor
      : FunctorEqual
        (ChainFunctor.functor F₁)
        (ChainFunctor.functor F₂)

  open FunctorEqual functor public

  field

    functor'
      : (x : ChainCategory.Object C)
      → ChainFunctorEqual
        (ChainFunctor.functor' F₁ x)
        (ChainFunctor.functor' F₂ x)

module ChainFunctorEqual
  = ChainFunctorEqual'

-- ### ChainFunctorIdentity

ChainFunctorIdentity {n = zero}
  = Chain₀FunctorIdentity
ChainFunctorIdentity {n = suc _}
  = ChainFunctorIdentity'

record ChainFunctorIdentity' {_ C} F where

  inductive

  field

    functor
      : FunctorIdentity
        (ChainFunctor.functor F)

  open FunctorIdentity functor public

  field

    functor'
      : (x : ChainCategory.Object C)
      → ChainFunctorIdentity
        (ChainFunctor.functor' F x)

module ChainFunctorIdentity
  = ChainFunctorIdentity'

-- ### ChainFunctorCompose

ChainFunctorCompose {n = zero}
  = Chain₀FunctorCompose
ChainFunctorCompose {n = suc _}
  = ChainFunctorCompose'

record ChainFunctorCompose' {_ C} F G H where

  inductive

  field

    functor
      : FunctorCompose
        (ChainFunctor.functor F)
        (ChainFunctor.functor G)
        (ChainFunctor.functor H)

  open FunctorCompose functor public

  field

    functor'
      : (x : ChainCategory.Object C)
      → ChainFunctorCompose
        (ChainFunctor.functor' F (ChainFunctor.base G x))
        (ChainFunctor.functor' G x)
        (ChainFunctor.functor' H x)

module ChainFunctorCompose
  = ChainFunctorCompose'

-- ### ChainFunctorSquare

ChainFunctorSquare {n = zero}
  = Chain₀FunctorSquare
ChainFunctorSquare {n = suc _}
  = ChainFunctorSquare'

record ChainFunctorSquare' {_ C₁} F G H₁ H₂ where

  inductive

  field

    functor
      : FunctorSquare
        (ChainFunctor.functor F)
        (ChainFunctor.functor G)
        (ChainFunctor.functor H₁)
        (ChainFunctor.functor H₂)

  open FunctorSquare functor public

  field

    functor'
      : (x₁ : ChainCategory.Object C₁)
      → ChainFunctorSquare
        (ChainFunctor.functor' F x₁) 
        (ChainFunctor.functor' G (ChainFunctor.base H₁ x₁))
        (ChainFunctor.functor' H₁ x₁) 
        (ChainFunctor.functor' H₂ (ChainFunctor.base F x₁))

module ChainFunctorSquare
  = ChainFunctorSquare'

-- ## Construction

-- ### ChainCategory

chain₁-category
  : Category
  → ChainCategory (suc zero)
chain₁-category C
  = record
  { category
    = C
  ; category'
    = λ _ → nil
  ; functor
    = λ _ → nil
  ; functor-equal
    = λ _ → nil
  ; functor-identity
    = λ _ → nil
  ; functor-compose
    = λ _ _ → nil
  }

-- ### ChainFunctor

chain₁-functor
  : {C D : Category}
  → Functor C D
  → ChainFunctor
    (chain₁-category C)
    (chain₁-category D)
chain₁-functor F
  = record
  { functor
    = F
  ; functor'
    = λ _ → nil
  ; functor-square
    = λ _ → nil
  }

-- ### ChainFunctorEqual

chain₁-functor-equal
  : {C D : Category}
  → {F₁ F₂ : Functor C D}
  → FunctorEqual F₁ F₂
  → ChainFunctorEqual
    (chain₁-functor F₁)
    (chain₁-functor F₂)
chain₁-functor-equal p
  = record
  { functor
    = p
  ; functor'
    = λ _ → nil
  }

-- ### ChainFunctorIdentity

chain₁-functor-identity
  : {C : Category}
  → {F : Functor C C}
  → FunctorIdentity F
  → ChainFunctorIdentity
    (chain₁-functor F)
chain₁-functor-identity p
  = record
  { functor
    = p
  ; functor'
    = λ _ → nil
  }

-- ### ChainFunctorCompose

chain₁-functor-compose
  : {C D E : Category}
  → {F : Functor D E}
  → {G : Functor C D}
  → {H : Functor C E}
  → FunctorCompose F G H
  → ChainFunctorCompose
    (chain₁-functor F)
    (chain₁-functor G)
    (chain₁-functor H)
chain₁-functor-compose p
  = record
  { functor
    = p
  ; functor'
    = λ _ → nil
  }

-- ### ChainFunctorSquare

chain₁-functor-square
  : {C₁ C₂ D₁ D₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → FunctorSquare F G H₁ H₂
  → ChainFunctorSquare
    (chain₁-functor F)
    (chain₁-functor G)
    (chain₁-functor H₁)
    (chain₁-functor H₂)
chain₁-functor-square s
  = record
  { functor
    = s
  ; functor'
    = λ _ → nil
  }

