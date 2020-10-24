module Prover.Category.Unit where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare)
open import Prover.Function
  using (Function; FunctionCompose; FunctionEqual; FunctionIdentity;
    FunctionSquare)
open import Prover.Prelude

-- ## Category

-- ### Function

module CategoryUnit
  (A : Set)
  where

  Object
    : Set
  Object
    = A

  record Arrow
    (x y : Object)
    : Set
    where

    constructor

      arrow

  ArrowEqual
    : {x y : Object}
    → Arrow x y
    → Arrow x y
    → Set
  ArrowEqual f₁ f₂
    = f₁ ≡ f₂

  abstract

    arrow-refl
      : {x y : Object}
      → {f : Arrow x y}
      → ArrowEqual f f
    arrow-refl
      = refl

    arrow-sym
      : {x y : Object}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁
    arrow-sym
      = sym

    arrow-trans
      : {x y : Object}
      → {f₁ f₂ f₃ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃
    arrow-trans
      = trans

    simplify
      : {x y : Object}
      → Arrow x y
      → Arrow x y
    simplify
      = id

    simplify-equal
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (simplify f) f
    simplify-equal _
      = arrow-refl

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

    compose-equal
      : {x y z : Object}
      → {f₁ f₂ : Arrow y z}
      → {g₁ g₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual g₁ g₂
      → ArrowEqual
        (compose f₁ g₁)
        (compose f₂ g₂)
    compose-equal _ _
      = refl

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (compose f (identity x)) f
    precompose _
      = refl

    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (compose (identity y) f) f
    postcompose _
      = refl

    associative
      : {w x y z : Object}
      → (f : Arrow y z)
      → (g : Arrow x y)
      → (h : Arrow w x)
      → ArrowEqual
        (compose (compose f g) h)
        (compose f (compose g h))
    associative _ _ _
      = refl

category-unit
  : Set
  → Category
category-unit A
  = record {CategoryUnit A}

-- ### Equality

arrow-equal-unit
  : {A : Set}
  → {x₁ x₂ y₁ y₂ : A}
  → {f₁ : CategoryUnit.Arrow A x₁ y₁}
  → {f₂ : CategoryUnit.Arrow A x₂ y₂}
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → Category.ArrowEqual' (category-unit A) f₁ f₂
arrow-equal-unit {A = A} refl refl
  = Category.arrow-refl' (category-unit A)

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

      map-equal
        : {x y : Category.Object (category-unit A)}
        → {f₁ f₂ : Category.Arrow (category-unit A) x y}
        → Category.ArrowEqual (category-unit A) f₁ f₂
        → Category.ArrowEqual (category-unit B) (map f₁) (map f₂)
      map-equal _
        = refl

      map-identity
        : (x : Category.Object (category-unit A))
        → Category.ArrowEqual (category-unit B)
          (map (Category.identity (category-unit A) x))
          (Category.identity (category-unit B) (base x))
      map-identity _
        = refl

      map-compose
        : {x y z : Category.Object (category-unit A)}
        → (f : Category.Arrow (category-unit A) y z)
        → (g : Category.Arrow (category-unit A) x y)
        → Category.ArrowEqual (category-unit B)
          (map (Category.compose (category-unit A) f g))
          (Category.compose (category-unit B) (map f) (map g))
      map-compose _ _
        = refl

  functor-unit
    : Function A B
    → Functor
      (category-unit A)
      (category-unit B)
  functor-unit F
    = record {FunctorUnit F}

-- ## FunctorEqual

functor-equal-unit
  : {A B : Set}
  → {F₁ F₂ : Function A B}
  → FunctionEqual F₁ F₂
  → FunctorEqual
    (functor-unit F₁)
    (functor-unit F₂)
functor-equal-unit p
  = record
  { FunctionEqual p
  ; map
    = λ {x₁ = x} {y₁ = y} _ → arrow-equal-unit
      (FunctionEqual.base p x)
      (FunctionEqual.base p y)
  }

-- ## FunctorIdentity

functor-identity-unit
  : {A : Set}
  → {F : Function A A}
  → FunctionIdentity F
  → FunctorIdentity
    (functor-unit F)
functor-identity-unit p
  = record
  { FunctionIdentity p
  ; map
    = λ {x₁ = x} {y₁ = y} _ → arrow-equal-unit
      (FunctionIdentity.base p x)
      (FunctionIdentity.base p y)
  }

-- ## FunctorCompose

functor-compose-unit
  : {A B C : Set}
  → {F : Function B C}
  → {G : Function A B}
  → {H : Function A C}
  → FunctionCompose F G H
  → FunctorCompose
    (functor-unit F)
    (functor-unit G)
    (functor-unit H)
functor-compose-unit p
  = record
  { FunctionCompose p
  ; map
    = λ {x} {y} _ → arrow-equal-unit
      (FunctionCompose.base p x)
      (FunctionCompose.base p y)
  }

-- ## FunctorSquare

functor-square-unit
  : {A₁ A₂ B₁ B₂ : Set}
  → {F : Function A₁ A₂}
  → {G : Function B₁ B₂}
  → {H₁ : Function A₁ B₁}
  → {H₂ : Function A₂ B₂}
  → FunctionSquare F G H₁ H₂
  → FunctorSquare
    (functor-unit F)
    (functor-unit G)
    (functor-unit H₁)
    (functor-unit H₂)
functor-square-unit s
  = record
  { FunctionSquare s
  ; map
    = λ {x₁ = x₁} {y₁ = y₁} _ → arrow-equal-unit
      (FunctionSquare.base s x₁)
      (FunctionSquare.base s y₁)
  }

