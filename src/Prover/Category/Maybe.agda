module Prover.Category.Maybe where

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

module CategoryMaybe
  (C : Category)
  where

  Object
    : Set
  Object
    = Category.Object C

  Arrow
    : Object
    → Object
    → Set
  Arrow x y
    = Maybe
      (Category.Arrow C x y)

  data ArrowEqual
    {x y : Object}
    : Arrow x y
    → Arrow x y
    → Set
    where

    nothing
      : ArrowEqual nothing nothing

    just
      : {f₁ f₂ : Category.Arrow C x y}
      → Category.ArrowEqual C f₁ f₂
      → ArrowEqual (just f₁) (just f₂)

  abstract

    arrow-refl
      : {x y : Object}
      → {f : Arrow x y}
      → ArrowEqual f f
    arrow-refl {f = nothing}
      = nothing
    arrow-refl {f = just _}
      = just (Category.arrow-refl C)

    arrow-sym
      : {x y : Object}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁
    arrow-sym nothing
      = nothing
    arrow-sym (just p)
      = just (Category.arrow-sym C p)

    arrow-trans
      : {x y : Object}
      → {f₁ f₂ f₃ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃
    arrow-trans nothing nothing
      = nothing
    arrow-trans (just p₁) (just p₂) 
      = just (Category.arrow-trans C p₁ p₂)

    simplify
      : {x y : Object}
      → Arrow x y
      → Arrow x y
    simplify nothing
      = nothing
    simplify (just f)
      = just (Category.simplify C f)

    simplify-equal
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (simplify f) f
    simplify-equal nothing
      = nothing
    simplify-equal (just f)
      = just (Category.simplify-equal C f)

  identity
    : (x : Object)
    → Arrow x x
  identity x
    = just (Category.identity C x)

  compose
    : {x y z : Object}
    → Arrow y z
    → Arrow x y
    → Arrow x z
  compose nothing _
    = nothing
  compose _ nothing
    = nothing
  compose (just f) (just g)
    = just (Category.compose C f g)

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
    compose-equal nothing _
      = nothing
    compose-equal (just _) nothing
      = nothing
    compose-equal (just p) (just q)
      = just (Category.compose-equal C p q)

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (compose f (identity x)) f
    precompose nothing
      = nothing
    precompose (just f)
      = just (Category.precompose C f)
  
    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (compose (identity y) f) f
    postcompose nothing
      = nothing
    postcompose (just f)
      = just (Category.postcompose C f)
  
    associative
      : {x y z w : Object}
      → (f : Arrow z w)
      → (g : Arrow y z)
      → (h : Arrow x y)
      → ArrowEqual
        (compose (compose f g) h)
        (compose f (compose g h))
    associative nothing _ _
      = nothing
    associative (just _) nothing _
      = nothing
    associative (just _) (just _) nothing
      = nothing
    associative (just f) (just g) (just h)
      = just (Category.associative C f g h)

category-maybe
  : Category
  → Category
category-maybe C
  = record {CategoryMaybe C}

-- ### Equality

arrow-equal-nothing
  : (C : Category)
  → {x₁ x₂ y₁ y₂ : Category.Object C}
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → Category.ArrowEqual'
    (category-maybe C)
    {x₁ = x₁}
    {y₁ = y₁}
    {x₂ = x₂}
    {y₂ = y₂}
    nothing
    nothing
arrow-equal-nothing C refl refl
  = Category.arrow-refl' (category-maybe C)

arrow-equal-just
  : (C : Category)
  → {x₁ x₂ y₁ y₂ : Category.Object C}
  → {f₁ : Category.Arrow C x₁ y₁}
  → {f₂ : Category.Arrow C x₂ y₂}
  → Category.ArrowEqual' C f₁ f₂
  → Category.ArrowEqual'
    (category-maybe C)
    (just f₁)
    (just f₂)
arrow-equal-just _ (any p)
  = any (CategoryMaybe.just p)

-- ## Functor

-- ### Function

module _
  {C D : Category}
  where

  module FunctorMaybe
    (F : Functor C D)
    where

    open Functor F public
      using (base)

    map
      : {x y : Category.Object (category-maybe C)}
      → Category.Arrow (category-maybe C) x y
      → Category.Arrow (category-maybe D) (base x) (base y)
    map
      = Maybe.map (Functor.map F)

    abstract

      map-equal
        : {x y : Category.Object (category-maybe C)}
        → {f₁ f₂ : Category.Arrow (category-maybe C) x y}
        → Category.ArrowEqual (category-maybe C) f₁ f₂
        → Category.ArrowEqual (category-maybe D) (map f₁) (map f₂)
      map-equal CategoryMaybe.nothing
        = CategoryMaybe.nothing
      map-equal (CategoryMaybe.just p)
        = CategoryMaybe.just (Functor.map-equal F p)

      map-identity
        : (x : Category.Object (category-maybe C))
        → Category.ArrowEqual (category-maybe D)
          (map (Category.identity (category-maybe C) x))
          (Category.identity (category-maybe D) (base x))
      map-identity x
        = CategoryMaybe.just (Functor.map-identity F x)
  
      map-compose
        : {x y z : Category.Object (category-maybe C)}
        → (f : Category.Arrow (category-maybe C) y z)
        → (g : Category.Arrow (category-maybe C) x y)
        → Category.ArrowEqual (category-maybe D)
          (map (Category.compose (category-maybe C) f g))
          (Category.compose (category-maybe D) (map f) (map g))
      map-compose nothing _
        = CategoryMaybe.nothing
      map-compose (just _) nothing
        = CategoryMaybe.nothing
      map-compose (just f) (just g)
        = CategoryMaybe.just (Functor.map-compose F f g)

  functor-maybe
    : Functor C D
    → Functor
      (category-maybe C)
      (category-maybe D)
  functor-maybe F
    = record {FunctorMaybe F}

-- ### Identity

module FunctorMaybeIdentity
  (C : Category)
  where

  base
    : (x : Category.Object (category-maybe C))
    → Functor.base (functor-maybe (functor-identity' C)) x
      ≅ Functor.base (functor-identity' (category-maybe C)) x
  base _
    = refl

  map
    : {x y : Category.Object (category-maybe C)}
    → (f : Category.Arrow (category-maybe C) x y)
    → Category'.ArrowEqual'
      (category-maybe C)
      (category-maybe C)
      (Functor.map (functor-maybe (functor-identity' C)) f)
      (Functor.map (functor-identity' (category-maybe C)) f)
  map nothing
    = Category.arrow-refl' (category-maybe C)
  map (just _)
    = Category.arrow-refl' (category-maybe C)

functor-maybe-identity
  : (C : Category)
  → FunctorEqual
    (functor-maybe (functor-identity' C))
    (functor-identity' (category-maybe C))
functor-maybe-identity C
  = record {FunctorMaybeIdentity C}

-- ### Compose

module _
  {C D E : Category}
  where

  module FunctorMaybeCompose
    (F : Functor D E) 
    (G : Functor C D) 
    where

    base
      : (x : Category.Object (category-maybe C))
      → Functor.base (functor-maybe (functor-compose' F G)) x
        ≅ Functor.base (functor-compose' (functor-maybe F) (functor-maybe G)) x
    base _
      = refl

    map
      : {x y : Category.Object (category-maybe C)}
      → (f : Category.Arrow (category-maybe C) x y)
      → Category'.ArrowEqual'
        (category-maybe E)
        (category-maybe E)
        (Functor.map (functor-maybe (functor-compose' F G)) f)
        (Functor.map (functor-compose' (functor-maybe F) (functor-maybe G)) f)
    map nothing
      = Category.arrow-refl' (category-maybe E)
    map (just _)
      = Category.arrow-refl' (category-maybe E)

  functor-maybe-compose
    : (F : Functor D E) 
    → (G : Functor C D) 
    → FunctorEqual
      (functor-maybe (functor-compose' F G))
      (functor-compose' (functor-maybe F) (functor-maybe G))
  functor-maybe-compose F G
    = record {FunctorMaybeCompose F G}

-- ## FunctorEqual

module _
  {C D : Category}
  {F₁ F₂ : Functor C D}
  where

  module FunctorEqualMaybe
    (p : FunctorEqual F₁ F₂)
    where

    open FunctorEqual p public
      using (base)

    map
      : {x y : Category.Object (category-maybe C)}
      → (f : Category.Arrow (category-maybe C) x y)
      → Category'.ArrowEqual'
        (category-maybe D)
        (category-maybe D)
        (Functor.map (functor-maybe F₁) f)
        (Functor.map (functor-maybe F₂) f)
    map {x = x} {y = y} nothing
      = arrow-equal-nothing D
        (FunctorEqual.base p x)
        (FunctorEqual.base p y)
    map (just f)
      = arrow-equal-just D
        (FunctorEqual.map p f)

  functor-equal-maybe
    : FunctorEqual F₁ F₂
    → FunctorEqual
      (functor-maybe F₁)
      (functor-maybe F₂)
  functor-equal-maybe p
    = record {FunctorEqualMaybe p}

functor-equal-maybe'
  : {A : Set}
  → {x₁ x₂ : A}
  → {C : Category}
  → (D : A → Category)
  → {F₁ : Functor C (D x₁)}
  → {F₂ : Functor C (D x₂)}
  → x₁ ≡ x₂
  → FunctorEqual F₁ F₂
  → FunctorEqual
    (functor-maybe F₁)
    (functor-maybe F₂)
functor-equal-maybe' _ refl
  = functor-equal-maybe

-- ## FunctorIdentity

functor-identity-maybe
  : {C : Category}
  → {F : Functor C C}
  → FunctorIdentity F
  → FunctorIdentity
    (functor-maybe F)
functor-identity-maybe {C = C} p
  = functor-identity-from-equal
  $ functor-trans (functor-equal-maybe
    (functor-identity-to-equal p))
  $ functor-maybe-identity C

functor-identity-maybe'
  : {A : Set}
  → {x₁ x₂ : A}
  → (C : A → Category)
  → {F : Functor (C x₂) (C x₁)}
  → x₁ ≡ x₂
  → FunctorIdentity F
  → FunctorIdentity
    (functor-maybe F)
functor-identity-maybe' _ refl
  = functor-identity-maybe

-- ## FunctorCompose

functor-compose-maybe
  : {C D E : Category}
  → {F : Functor D E}
  → {G : Functor C D}
  → {H : Functor C E}
  → FunctorCompose F G H
  → FunctorCompose
    (functor-maybe F)
    (functor-maybe G)
    (functor-maybe H)
functor-compose-maybe {F = F} {G = G} p
  = functor-compose-from-equal
    (functor-maybe F)
    (functor-maybe G)
  $ functor-trans (functor-equal-maybe
    (functor-compose-to-equal p))
  $ functor-maybe-compose F G

functor-compose-maybe'
  : {A : Set}
  → {x₁ x₂ : A}
  → {C D : Category}
  → (E : A → Category)
  → {F : Functor D (E x₂)}
  → {G : Functor C D}
  → {H : Functor C (E x₁)}
  → x₁ ≡ x₂
  → FunctorCompose F G H
  → FunctorCompose
    (functor-maybe F)
    (functor-maybe G)
    (functor-maybe H)
functor-compose-maybe' _ refl
  = functor-compose-maybe

-- ## FunctorSquare

functor-square-maybe
  : {C₁ C₂ D₁ D₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → FunctorSquare F G H₁ H₂
  → FunctorSquare
    (functor-maybe F)
    (functor-maybe G)
    (functor-maybe H₁)
    (functor-maybe H₂)
functor-square-maybe {F = F} {G = G} {H₁ = H₁} {H₂ = H₂} s
  = functor-square-from-equal
    (functor-maybe F)
    (functor-maybe G)
    (functor-maybe H₁)
    (functor-maybe H₂)
  $ functor-trans (functor-sym
    (functor-maybe-compose H₂ F))
  $ functor-trans (functor-equal-maybe
    (functor-square-to-equal s))
  $ functor-maybe-compose G H₁

functor-square-maybe'
  : {A : Set}
  → {x₁ x₂ : A}
  → {C₁ C₂ D₁ : Category}
  → (D₂ : A → Category)
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ (D₂ x₂)}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ (D₂ x₁)}
  → x₁ ≡ x₂
  → FunctorSquare F G H₁ H₂
  → FunctorSquare
    (functor-maybe F)
    (functor-maybe G)
    (functor-maybe H₁)
    (functor-maybe H₂)
functor-square-maybe' _ refl
  = functor-square-maybe

