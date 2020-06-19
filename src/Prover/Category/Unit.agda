module Prover.Category.Unit where

open import Prover.Category
  using (Category; DependentCategory; Functor; FunctorCompose; FunctorIdentity;
    FunctorSquare)
open import Prover.Category.Base
  using (Function; FunctionCompose; FunctionIdentity; FunctionSquare)
open import Prover.Category.Simple
  using (SimpleDependentCategory)
open import Prover.Prelude

-- ## Category

module CategoryUnit
  (A : Set)
  where

  Object
    : Set
  Object
    = A

  record Arrow
    (x : Object)
    (y : Object)
    : Set
    where

    constructor

      arrow

  identity
    : (x : Object)
    → Arrow x x
  identity _
    = arrow

  compose
    : {x y z : Object}
    → Arrow y z
    → Arrow x y
    → Arrow x z
  compose _ _
    = arrow

  abstract

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose f (identity x) ≡ f
    precompose arrow
      = refl
  
    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose (identity y) f ≡ f
    postcompose arrow
      = refl
  
    associative
      : {w x y z : Object}
      → (f : Arrow y z)
      → (g : Arrow x y)
      → (h : Arrow w x)
      → compose (compose f g) h ≡ compose f (compose g h)
    associative arrow arrow arrow
      = refl

category-unit
  : Set
  → Category
category-unit A
  = record {CategoryUnit A}

-- ## Functor

module _
  {A B : Set}
  where

  module FunctorUnit
    (f : Function A B)
    where

    base
      : Category.Object (category-unit A)
      → Category.Object (category-unit B)
    base
      = f

    map
      : {x y : Category.Object (category-unit A)}
      → Category.Arrow (category-unit A) x y
      → Category.Arrow (category-unit B) (base x) (base y)
    map _
      = CategoryUnit.arrow

    abstract

      map-identity
        : (x : Category.Object (category-unit A))
        → map (Category.identity (category-unit A) x)
          ≡ Category.identity (category-unit B) (base x)
      map-identity _
        = refl
  
      map-compose
        : {x y z : Category.Object (category-unit A)}
        → (f : Category.Arrow (category-unit A) y z)
        → (g : Category.Arrow (category-unit A) x y)
        → map (Category.compose (category-unit A) f g)
          ≡ Category.compose (category-unit B) (map f) (map g)
      map-compose _ _
        = refl

  functor-unit
    : Function A B
    → Functor
      (category-unit A)
      (category-unit B)
  functor-unit f
    = record {FunctorUnit f}
  
-- ## FunctorIdentity

module _
  {A : Set}
  where

  module FunctorIdentityUnit
    (f : Function A A)
    (p : FunctionIdentity f)
    where

    base
      : (x : Category.Object (category-unit A))
      → Functor.base (functor-unit f) x ≅ x
    base
      = p

    map
      : {x y : Category.Object (category-unit A)}
      → (f' : Category.Arrow (category-unit A) x y)
      → Functor.map (functor-unit f) f' ≅ f'
    map {x = x} {y = y} CategoryUnit.arrow
      = Category.arrow-eq (category-unit A) (p x) (p y) CategoryUnit.arrow

  functor-identity-unit
    : (f : Function A A)
    → FunctionIdentity f
    → FunctorIdentity
      (functor-unit f)
  functor-identity-unit f p
    = record {FunctorIdentityUnit f p}

-- ## FunctorCompose

module _
  {A B C : Set}
  where

  module FunctorComposeUnit
    (f : Function B C)
    (g : Function A B)
    (h : Function A C)
    (p : FunctionCompose f g h)
    where

    base
      : (x : Category.Object (category-unit A))
      → Functor.base (functor-unit h) x
        ≅ Functor.base (functor-unit f) (Functor.base (functor-unit g) x)
    base
      = p

    map
      : {x y : Category.Object (category-unit A)}
      → (f' : Category.Arrow (category-unit A) x y)
      → Functor.map (functor-unit h) f'
        ≅ Functor.map (functor-unit f) (Functor.map (functor-unit g) f')
    map {x = x} {y = y} _
      = Category.arrow-eq (category-unit C) (p x) (p y) CategoryUnit.arrow

  functor-compose-unit
    : (f : Function B C)
    → (g : Function A B)
    → (h : Function A C)
    → FunctionCompose f g h
    → FunctorCompose
      (functor-unit f)
      (functor-unit g)
      (functor-unit h)
  functor-compose-unit f g h p
    = record {FunctorComposeUnit f g h p}

-- ## FunctorSquare

module _
  {A₁ A₂ B₁ B₂ : Set}
  where

  module FunctorSquareUnit
    (f : Function A₁ A₂)
    (g : Function B₁ B₂)
    (h₁ : Function A₁ B₁)
    (h₂ : Function A₂ B₂)
    (s : FunctionSquare f g h₁ h₂)
    where

    base
      : (x₁ : Category.Object (category-unit A₁))
      → Functor.base (functor-unit h₂) (Functor.base (functor-unit f) x₁) 
        ≅ Functor.base (functor-unit g) (Functor.base (functor-unit h₁) x₁)
    base
      = s
  
    map
      : {x₁ y₁ : Category.Object (category-unit A₁)}
      → (f₁' : Category.Arrow (category-unit A₁) x₁ y₁)
      → Functor.map (functor-unit h₂) (Functor.map (functor-unit f) f₁')
        ≅ Functor.map (functor-unit g) (Functor.map (functor-unit h₁) f₁')
    map {x₁ = x₁} {y₁ = y₁} _
      = Category.arrow-eq (category-unit B₂) (s x₁) (s y₁) CategoryUnit.arrow

  functor-square-unit
    : (f : Function A₁ A₂)
    → (g : Function B₁ B₂)
    → (h₁ : Function A₁ B₁)
    → (h₂ : Function A₂ B₂)
    → FunctionSquare f g h₁ h₂
    → FunctorSquare
      (functor-unit f)
      (functor-unit g)
      (functor-unit h₁)
      (functor-unit h₂)
  functor-square-unit f g h₁ h₂ s
    = record {FunctorSquareUnit f g h₁ h₂ s}

-- ## DependentCategory

module _
  {C : Category}
  where

  module DependentCategoryUnit
    (A : SimpleDependentCategory C)
    where

    category
      : Category.Object C
      → Category
    category x
      = category-unit
        (SimpleDependentCategory.set A x)

    functor
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → Functor
        (category x)
        (category y)
    functor f
      = functor-unit
        (SimpleDependentCategory.function A f)

    abstract

      functor-identity
        : (x : Category.Object C)
        → FunctorIdentity
          (functor (Category.identity C x))
      functor-identity x
        = functor-identity-unit
          (SimpleDependentCategory.function A (Category.identity C x))
          (SimpleDependentCategory.function-identity A x)
  
      functor-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → FunctorCompose
          (functor f)
          (functor g)
          (functor (Category.compose C f g))
      functor-compose f g
        = functor-compose-unit
          (SimpleDependentCategory.function A f)
          (SimpleDependentCategory.function A g)
          (SimpleDependentCategory.function A (Category.compose C f g))
          (SimpleDependentCategory.function-compose A f g)

  dependent-category-unit
    : SimpleDependentCategory C
    → DependentCategory C
  dependent-category-unit A
    = record {DependentCategoryUnit A}

