module Prover.Category.Product where

open import Prover.Category
  using (module Category'; Category; Functor; FunctorCompose; FunctorEqual;
    FunctorIdentity; FunctorSquare; any; functor-compose';
    functor-compose-from-equal; functor-compose-to-equal; functor-identity';
    functor-identity-from-equal; functor-identity-to-equal;
    functor-square-from-equal; functor-square-to-equal; functor-sym;
    functor-trans)
open import Prover.Prelude

-- ## Category

-- ### Function

module CategoryProduct
  (C₁ : Category)
  (C₂ : Category)
  where

  Object
    : Set
  Object
    = Category.Object C₁
    × Category.Object C₂

  Arrow
    : Object
    → Object
    → Set
  Arrow (x₁ , x₂) (y₁ , y₂)
    = Category.Arrow C₁ x₁ y₁
    × Category.Arrow C₂ x₂ y₂

  ArrowEqual
    : {x y : Object}
    → Arrow x y
    → Arrow x y
    → Set
  ArrowEqual (x₁ , x₂) (y₁ , y₂)
    = Category.ArrowEqual C₁ x₁ y₁
    × Category.ArrowEqual C₂ x₂ y₂

  abstract

    arrow-refl
      : {x y : Object}
      → {f : Arrow x y}
      → ArrowEqual f f
    arrow-refl
      = Category.arrow-refl C₁
      , Category.arrow-refl C₂

    arrow-sym
      : {x y : Object}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁
    arrow-sym (p₁ , p₂)
      = Category.arrow-sym C₁ p₁
      , Category.arrow-sym C₂ p₂

    arrow-trans
      : {x y : Object}
      → {f₁ f₂ f₃ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃
    arrow-trans (p₁₁ , p₁₂) (p₂₁ , p₂₂)
      = Category.arrow-trans C₁ p₁₁ p₂₁
      , Category.arrow-trans C₂ p₁₂ p₂₂

    simplify
      : {x y : Object}
      → Arrow x y
      → Arrow x y
    simplify (f₁ , f₂)
      = Category.simplify C₁ f₁
      , Category.simplify C₂ f₂

    simplify-equal
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (simplify f) f
    simplify-equal (f₁ , f₂)
      = Category.simplify-equal C₁ f₁
      , Category.simplify-equal C₂ f₂

  identity
    : (x : Object)
    → Arrow x x
  identity (x₁ , x₂)
    = Category.identity C₁ x₁
    , Category.identity C₂ x₂

  compose
    : {x y z : Object}
    → Arrow y z
    → Arrow x y
    → Arrow x z
  compose (f₁ , f₂) (g₁ , g₂)
    = Category.compose C₁ f₁ g₁
    , Category.compose C₂ f₂ g₂

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
    compose-equal (p₁ , p₂) (q₁ , q₂)
      = Category.compose-equal C₁ p₁ q₁
      , Category.compose-equal C₂ p₂ q₂

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (compose f (identity x)) f
    precompose (f₁ , f₂)
      = Category.precompose C₁ f₁
      , Category.precompose C₂ f₂

    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (compose (identity y) f) f
    postcompose (f₁ , f₂)
      = Category.postcompose C₁ f₁
      , Category.postcompose C₂ f₂

    associative
      : {w x y z : Object}
      → (f : Arrow y z)
      → (g : Arrow x y)
      → (h : Arrow w x)
      → ArrowEqual
        (compose (compose f g) h)
        (compose f (compose g h))
    associative (f₁ , f₂) (g₁ , g₂) (h₁ , h₂)
      = Category.associative C₁ f₁ g₁ h₁
      , Category.associative C₂ f₂ g₂ h₂

category-product
  : Category
  → Category
  → Category
category-product C₁ C₂
  = record {CategoryProduct C₁ C₂}

-- ### Equality

arrow-equal-product
  : {C₁ C₂ : Category}
  → {x₁₁ x₂₁ y₁₁ y₂₁ : Category.Object C₁}
  → {x₁₂ x₂₂ y₁₂ y₂₂ : Category.Object C₂}
  → {f₁₁ : Category.Arrow C₁ x₁₁ y₁₁}
  → {f₁₂ : Category.Arrow C₂ x₁₂ y₁₂}
  → {f₂₁ : Category.Arrow C₁ x₂₁ y₂₁}
  → {f₂₂ : Category.Arrow C₂ x₂₂ y₂₂}
  → Category.ArrowEqual' C₁ f₁₁ f₂₁
  → Category.ArrowEqual' C₂ f₁₂ f₂₂
  → Category.ArrowEqual' (category-product C₁ C₂) (f₁₁ , f₁₂) (f₂₁ , f₂₂)
arrow-equal-product (any p₁) (any p₂)
  = any (p₁ , p₂)

-- ## Functor

-- ### Function

module _
  {C₁ C₂ D₁ D₂ : Category}
  where

  module FunctorProduct
    (F₁ : Functor C₁ D₁)
    (F₂ : Functor C₂ D₂)
    where

    base
      : Category.Object (category-product C₁ C₂)
      → Category.Object (category-product D₁ D₂)
    base (x₁ , x₂)
      = Functor.base F₁ x₁
      , Functor.base F₂ x₂

    map
      : {x y : Category.Object (category-product C₁ C₂)}
      → Category.Arrow (category-product C₁ C₂) x y
      → Category.Arrow (category-product D₁ D₂) (base x) (base y)
    map (f₁ , f₂)
      = Functor.map F₁ f₁
      , Functor.map F₂ f₂

    abstract

      map-equal
        : {x y : Category.Object (category-product C₁ C₂)}
        → {f₁ f₂ : Category.Arrow (category-product C₁ C₂) x y}
        → Category.ArrowEqual (category-product C₁ C₂) f₁ f₂
        → Category.ArrowEqual (category-product D₁ D₂) (map f₁) (map f₂)
      map-equal (p₁ , p₂)
        = Functor.map-equal F₁ p₁
        , Functor.map-equal F₂ p₂

      map-identity
        : (x : Category.Object (category-product C₁ C₂))
        → Category.ArrowEqual (category-product D₁ D₂)
          (map (Category.identity (category-product C₁ C₂) x))
          (Category.identity (category-product D₁ D₂) (base x))
      map-identity (x₁ , x₂)
        = Functor.map-identity F₁ x₁
        , Functor.map-identity F₂ x₂

      map-compose
        : {x y z : Category.Object (category-product C₁ C₂)}
        → (f : Category.Arrow (category-product C₁ C₂) y z)
        → (g : Category.Arrow (category-product C₁ C₂) x y)
        → Category.ArrowEqual (category-product D₁ D₂)
          (map (Category.compose (category-product C₁ C₂) f g))
          (Category.compose (category-product D₁ D₂) (map f) (map g))
      map-compose (f₁ , f₂) (g₁ , g₂)
        = Functor.map-compose F₁ f₁ g₁
        , Functor.map-compose F₂ f₂ g₂

  functor-product
    : Functor C₁ D₁
    → Functor C₂ D₂
    → Functor
      (category-product C₁ C₂)
      (category-product D₁ D₂)
  functor-product F₁ F₂
    = record {FunctorProduct F₁ F₂}

-- ### Identity

functor-product-identity
  : (C₁ C₂ : Category)
  → FunctorEqual
    (functor-product (functor-identity' C₁) (functor-identity' C₂))
    (functor-identity' (category-product C₁ C₂))
functor-product-identity C₁ C₂
  = record
  { base
    = λ _ → refl
  ; map
    = λ _ → Category.arrow-refl' (category-product C₁ C₂)
  }

-- ### Compose

functor-product-compose
  : {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  → (F₁ : Functor D₁ E₁)
  → (F₂ : Functor D₂ E₂)
  → (G₁ : Functor C₁ D₁)
  → (G₂ : Functor C₂ D₂)
  → FunctorEqual
    (functor-product (functor-compose' F₁ G₁) (functor-compose' F₂ G₂))
    (functor-compose' (functor-product F₁ F₂) (functor-product G₁ G₂))
functor-product-compose {E₁ = E₁} {E₂ = E₂} _ _ _ _
  = record
  { base
    = λ _ → refl
  ; map
    = λ _ → Category.arrow-refl' (category-product E₁ E₂)
  }

-- ## FunctorEqual

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F₁₁ F₂₁ : Functor C₁ D₁}
  {F₁₂ F₂₂ : Functor C₂ D₂}
  where

  module FunctorEqualProduct
    (p₁ : FunctorEqual F₁₁ F₂₁)
    (p₂ : FunctorEqual F₁₂ F₂₂)
    where

    base
      : (x : Category.Object (category-product C₁ C₂))
      → Functor.base (functor-product F₁₁ F₁₂) x
        ≅ Functor.base (functor-product F₂₁ F₂₂) x
    base (x₁ , x₂)
      = Sigma.comma-equal
        (FunctorEqual.base p₁ x₁)
        (FunctorEqual.base p₂ x₂)
  
    map
      : {x y : Category.Object (category-product C₁ C₂)}
      → (f : Category.Arrow (category-product C₁ C₂) x y)
      → Category'.ArrowEqual'
        (category-product D₁ D₂)
        (category-product D₁ D₂)
        (Functor.map (functor-product F₁₁ F₁₂) f)
        (Functor.map (functor-product F₂₁ F₂₂) f)
    map (f₁ , f₂)
      = arrow-equal-product
        (FunctorEqual.map p₁ f₁)
        (FunctorEqual.map p₂ f₂)

  functor-equal-product
    : FunctorEqual F₁₁ F₂₁
    → FunctorEqual F₁₂ F₂₂
    → FunctorEqual
      (functor-product F₁₁ F₁₂)
      (functor-product F₂₁ F₂₂)
  functor-equal-product p₁ p₂
    = record {FunctorEqualProduct p₁ p₂}

-- ## FunctorIdentity

functor-identity-product
  : {C₁ C₂ : Category}
  → {F₁ : Functor C₁ C₁}
  → {F₂ : Functor C₂ C₂}
  → FunctorIdentity F₁
  → FunctorIdentity F₂
  → FunctorIdentity
    (functor-product F₁ F₂)
functor-identity-product
  {C₁ = C₁} {C₂ = C₂} p₁ p₂
  = functor-identity-from-equal
  $ functor-trans (functor-equal-product
    (functor-identity-to-equal p₁)
    (functor-identity-to-equal p₂))
  $ functor-product-identity C₁ C₂

-- ## FunctorCompose

functor-compose-product
  : {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  → {F₁ : Functor D₁ E₁}
  → {F₂ : Functor D₂ E₂}
  → {G₁ : Functor C₁ D₁}
  → {G₂ : Functor C₂ D₂}
  → {H₁ : Functor C₁ E₁}
  → {H₂ : Functor C₂ E₂}
  → FunctorCompose F₁ G₁ H₁
  → FunctorCompose F₂ G₂ H₂
  → FunctorCompose
    (functor-product F₁ F₂)
    (functor-product G₁ G₂)
    (functor-product H₁ H₂)
functor-compose-product
  {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p₁ p₂
  = functor-compose-from-equal
    (functor-product F₁ F₂)
    (functor-product G₁ G₂)
  $ functor-trans (functor-equal-product
    (functor-compose-to-equal p₁)
    (functor-compose-to-equal p₂))
  $ functor-product-compose F₁ F₂ G₁ G₂

-- ## FunctorSquare

functor-square-product
  : {C₁₁ C₁₂ C₂₁ C₂₂ D₁₁ D₁₂ D₂₁ D₂₂ : Category}
  → {F₁ : Functor C₁₁ C₂₁}
  → {F₂ : Functor C₁₂ C₂₂}
  → {G₁ : Functor D₁₁ D₂₁}
  → {G₂ : Functor D₁₂ D₂₂}
  → {H₁₁ : Functor C₁₁ D₁₁}
  → {H₁₂ : Functor C₁₂ D₁₂}
  → {H₂₁ : Functor C₂₁ D₂₁}
  → {H₂₂ : Functor C₂₂ D₂₂}
  → FunctorSquare F₁ G₁ H₁₁ H₂₁
  → FunctorSquare F₂ G₂ H₁₂ H₂₂
  → FunctorSquare
    (functor-product F₁ F₂)
    (functor-product G₁ G₂)
    (functor-product H₁₁ H₁₂)
    (functor-product H₂₁ H₂₂)
functor-square-product
  {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂}
  {H₁₁ = H₁₁} {H₁₂ = H₁₂} {H₂₁ = H₂₁} {H₂₂ = H₂₂} s₁ s₂
  = functor-square-from-equal
    (functor-product F₁ F₂)
    (functor-product G₁ G₂)
    (functor-product H₁₁ H₁₂)
    (functor-product H₂₁ H₂₂)
  $ functor-trans (functor-sym
    (functor-product-compose H₂₁ H₂₂ F₁ F₂))
  $ functor-trans (functor-equal-product
    (functor-square-to-equal s₁)
    (functor-square-to-equal s₂))
  $ functor-product-compose G₁ G₂ H₁₁ H₁₂

