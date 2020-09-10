module Prover.Category.Unit where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Function
  using (Function; FunctionCompose; FunctionIdentity; FunctionSquare)
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
    (F : Function A B)
    where

    open Function F public
      using (base)

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
  functor-unit F
    = record {FunctorUnit F}
  
-- ## FunctorIdentity

module _
  {A : Set}
  {F : Function A A}
  where

  module FunctorIdentityUnit
    (p : FunctionIdentity F)
    where

    open FunctionIdentity p public
      using (base)

    map
      : {x y : Category.Object (category-unit A)}
      → (f : Category.Arrow (category-unit A) x y)
      → Functor.map (functor-unit F) f ≅ f
    map {x = x} {y = y} CategoryUnit.arrow
      = Category.arrow-eq
        (category-unit A)
        (base x)
        (base y)
        CategoryUnit.arrow

  functor-identity-unit
    : FunctionIdentity F
    → FunctorIdentity
      (functor-unit F)
  functor-identity-unit p
    = record {FunctorIdentityUnit p}

-- ## FunctorCompose

module _
  {A B C : Set}
  {F : Function B C}
  {G : Function A B}
  {H : Function A C}
  where

  module FunctorComposeUnit
    (p : FunctionCompose F G H)
    where

    open FunctionCompose p public
      using (base)

    map
      : {x y : Category.Object (category-unit A)}
      → (f : Category.Arrow (category-unit A) x y)
      → Functor.map (functor-unit H) f
        ≅ Functor.map (functor-unit F) (Functor.map (functor-unit G) f)
    map {x = x} {y = y} _
      = Category.arrow-eq
        (category-unit C)
        (base x)
        (base y)
        CategoryUnit.arrow

  functor-compose-unit
    : FunctionCompose F G H
    → FunctorCompose
      (functor-unit F)
      (functor-unit G)
      (functor-unit H)
  functor-compose-unit p
    = record {FunctorComposeUnit p}

-- ## FunctorSquare

module _
  {A₁ A₂ B₁ B₂ : Set}
  {F : Function A₁ A₂}
  {G : Function B₁ B₂}
  {H₁ : Function A₁ B₁}
  {H₂ : Function A₂ B₂}
  where

  module FunctorSquareUnit
    (s : FunctionSquare F G H₁ H₂)
    where

    open FunctionSquare s public
      using (base)
  
    map
      : {x₁ y₁ : Category.Object (category-unit A₁)}
      → (f₁ : Category.Arrow (category-unit A₁) x₁ y₁)
      → Functor.map (functor-unit H₂) (Functor.map (functor-unit F) f₁)
        ≅ Functor.map (functor-unit G) (Functor.map (functor-unit H₁) f₁)
    map {x₁ = x₁} {y₁ = y₁} _
      = Category.arrow-eq
        (category-unit B₂)
        (base x₁)
        (base y₁)
        CategoryUnit.arrow

  functor-square-unit
    : FunctionSquare F G H₁ H₂
    → FunctorSquare
      (functor-unit F)
      (functor-unit G)
      (functor-unit H₁)
      (functor-unit H₂)
  functor-square-unit s
    = record {FunctorSquareUnit s}

