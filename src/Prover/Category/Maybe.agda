module Prover.Category.Maybe where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare; functor-compose'; functor-compose-from-equal;
    functor-compose-to-equal; functor-identity'; functor-identity-from-equal;
    functor-identity-to-equal; functor-square-from-equal;
    functor-square-to-equal; functor-sym; functor-trans)
open import Prover.Prelude

-- ## Category

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
    = Maybe (Category.Arrow C x y)

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

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose f (identity x) ≡ f
    precompose nothing
      = refl
    precompose (just f)
      = sub just (Category.precompose C f)
  
    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose (identity y) f ≡ f
    postcompose nothing
      = refl
    postcompose (just f)
      = sub just (Category.postcompose C f)
  
    associative
      : {x y z w : Object}
      → (f : Arrow z w)
      → (g : Arrow y z)
      → (h : Arrow x y)
      → compose (compose f g) h ≡ compose f (compose g h)
    associative nothing _ _
      = refl
    associative (just _) nothing _
      = refl
    associative (just _) (just _) nothing
      = refl
    associative (just f) (just g) (just h)
      = sub just (Category.associative C f g h)

category-maybe
  : Category
  → Category
category-maybe C
  = record {CategoryMaybe C}

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

      map-identity
        : (x : Category.Object (category-maybe C))
        → map (Category.identity (category-maybe C) x)
          ≡ Category.identity (category-maybe D) (base x)
      map-identity x
        = sub just (Functor.map-identity F x)
  
      map-compose
        : {x y z : Category.Object (category-maybe C)}
        → (f : Category.Arrow (category-maybe C) y z)
        → (g : Category.Arrow (category-maybe C) x y)
        → map (Category.compose (category-maybe C) f g)
          ≡ Category.compose (category-maybe D) (map f) (map g)
      map-compose nothing _
        = refl
      map-compose (just _) nothing
        = refl
      map-compose (just f) (just g)
        = sub just (Functor.map-compose F f g)

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
    → Functor.map (functor-maybe (functor-identity' C)) f
      ≅ Functor.map (functor-identity' (category-maybe C)) f
  map nothing
    = refl
  map (just _)
    = refl

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
      → Functor.map (functor-maybe (functor-compose' F G)) f
        ≅ Functor.map (functor-compose' (functor-maybe F) (functor-maybe G)) f
    map nothing
      = refl
    map (just _)
      = refl

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
      → Functor.map (functor-maybe F₁) f ≅ Functor.map (functor-maybe F₂) f
    map {x = x} {y = y} nothing
      = Maybe.nothing-eq₂
        (Category.Arrow D)
        (base x)
        (base y)
    map {x = x} {y = y} (just f)
      = Maybe.just-eq₂
        (Category.Arrow D)
        (base x)
        (base y)
        (FunctorEqual.map p f)

  functor-equal-maybe
    : FunctorEqual F₁ F₂
    → FunctorEqual
      (functor-maybe F₁)
      (functor-maybe F₂)
  functor-equal-maybe p
    = record {FunctorEqualMaybe p}

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

functor-identity-maybe-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → (C : A → Category)
  → {F : Functor (C x₁) (C x₂)}
  → x₂ ≡ x₁
  → FunctorIdentity F
  → FunctorIdentity
    (functor-maybe F)
functor-identity-maybe-eq _ refl
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

functor-compose-maybe-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {C D : Category}
  → (E : A → Category)
  → {F : Functor D (E x₁)}
  → {G : Functor C D}
  → {H : Functor C (E x₂)}
  → x₂ ≡ x₁
  → FunctorCompose F G H
  → FunctorCompose
    (functor-maybe F)
    (functor-maybe G)
    (functor-maybe H)
functor-compose-maybe-eq _ refl
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

functor-square-maybe-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {C₁ C₂ D₁ : Category}
  → (D₂ : A → Category)
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ (D₂ x₁)}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ (D₂ x₂)}
  → x₂ ≡ x₁
  → FunctorSquare F G H₁ H₂
  → FunctorSquare
    (functor-maybe F)
    (functor-maybe G)
    (functor-maybe H₁)
    (functor-maybe H₂)
functor-square-maybe-eq _ refl
  = functor-square-maybe

