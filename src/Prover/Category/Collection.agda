module Prover.Category.Collection where

open import Prover.Category
  using (module Category'; Category; Functor; FunctorCompose; FunctorEqual;
    FunctorIdentity; FunctorSquare; any)
open import Prover.Category.List
  using (category-list; functor-compose-list; functor-equal-list;
    functor-identity-list; functor-list; functor-square-list)
open import Prover.Function.Relation
  using (FunctionInjective)
open import Prover.Prelude

-- ## Category

-- ### Function

module CategoryCollection
  (C : Category)
  (R : Relation (Category.Object C))
  where

  Object
    : Set
  Object
    = Collection R

  record Arrow
    (xs ys : Object)
    : Set
    where

    constructor

      arrow

    field

      elements
        : Category.Arrow
          (category-list C)
          (Collection.elements xs)
          (Collection.elements ys)

  record ArrowEqual
    {xs ys : Object}
    (fs₁ fs₂ : Arrow xs ys)
    : Set
    where

    constructor

      arrow-equal

    field

      elements
        : Category.ArrowEqual
          (category-list C)
          (Arrow.elements fs₁)
          (Arrow.elements fs₂)

  abstract

    arrow-refl
      : {xs ys : Object}
      → {fs : Arrow xs ys}
      → ArrowEqual fs fs
    arrow-refl
      = record
      { elements
        = Category.arrow-refl
          (category-list C)
      }

    arrow-sym
      : {xs ys : Object}
      → {fs₁ fs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₁
    arrow-sym (arrow-equal ps)
      = record
      { elements
        = Category.arrow-sym
          (category-list C) ps
      }

    arrow-trans
      : {xs ys : Object}
      → {fs₁ fs₂ fs₃ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₃
      → ArrowEqual fs₁ fs₃
    arrow-trans (arrow-equal ps₁) (arrow-equal ps₂)
      = record
      { elements
        = Category.arrow-trans
          (category-list C) ps₁ ps₂
      }

    simplify
      : {xs ys : Object}
      → Arrow xs ys
      → Arrow xs ys
    simplify (arrow fs)
      = record
      { elements
        = Category.simplify
          (category-list C) fs
      }

    simplify-equal
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (simplify fs) fs
    simplify-equal (arrow fs)
      = record
      { elements
        = Category.simplify-equal
          (category-list C) fs
      }

  identity
    : (xs : Object)
    → Arrow xs xs
  identity (collection xs _)
    = record
    { elements
      = Category.identity
        (category-list C) xs
    }

  compose
    : {xs ys zs : Object}
    → Arrow ys zs
    → Arrow xs ys
    → Arrow xs zs
  compose (arrow fs) (arrow gs)
    = record
    { elements
      = Category.compose
        (category-list C) fs gs
    }

  abstract

    compose-equal
      : {xs ys zs : Object}
      → {fs₁ fs₂ : Arrow ys zs}
      → {gs₁ gs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual gs₁ gs₂
      → ArrowEqual
        (compose fs₁ gs₁)
        (compose fs₂ gs₂)
    compose-equal (arrow-equal ps) (arrow-equal qs)
      = record
      { elements
        = Category.compose-equal
          (category-list C) ps qs
      }

    precompose
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (compose fs (identity xs)) fs
    precompose (arrow fs)
      = record
      { elements
        = Category.precompose
          (category-list C) fs
      }

    postcompose
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (compose (identity ys) fs) fs
    postcompose (arrow fs)
      = record
      { elements
        = Category.postcompose
          (category-list C) fs
      }

    associative
      : {ws xs ys zs : Object}
      → (fs : Arrow ys zs)
      → (gs : Arrow xs ys)
      → (hs : Arrow ws xs)
      → ArrowEqual
        (compose (compose fs gs) hs)
        (compose fs (compose gs hs))
    associative (arrow fs) (arrow gs) (arrow hs)
      = record
      { elements
        = Category.associative
          (category-list C) fs gs hs
      }

category-collection
  : (C : Category)
  → Relation (Category.Object C)
  → Category
category-collection C R
  = record {CategoryCollection C R}

-- ### Equality

arrow-equal-collection
  : {C : Category}
  → {R : Relation (Category.Object C)}
  → (xs₁ xs₂ ys₁ ys₂ : Collection R)
  → {fs₁ : Category.Arrow
    (category-list C)
    (Collection.elements xs₁)
    (Collection.elements ys₁)}
  → {fs₂ : Category.Arrow
    (category-list C)
    (Collection.elements xs₂)
    (Collection.elements ys₂)}
  → Category.ArrowEqual' (category-list C) fs₁ fs₂
  → Category.ArrowEqual'
    (category-collection C R)
    (CategoryCollection.arrow {xs = xs₁} {ys = ys₁} fs₁)
    (CategoryCollection.arrow {xs = xs₂} {ys = ys₂} fs₂)
arrow-equal-collection _ _ _ _ (any p)
  = Category.any
  $ record
  { elements
    = p
  }

-- ## Functor

module _
  {C D : Category}
  {R : Relation (Category.Object C)}
  {S : Relation (Category.Object D)}
  where

  module FunctorCollection
    (F : Functor C D)
    (i : FunctionInjective R S (Functor.function F))
    where

    base
      : Category.Object (category-collection C R)
      → Category.Object (category-collection D S)
    base
      = Collection.map S
        (Functor.base F)
        (FunctionInjective.base i)

    map
      : {xs ys : Category.Object (category-collection C R)}
      → Category.Arrow (category-collection C R) xs ys
      → Category.Arrow (category-collection D S) (base xs) (base ys)
    map (CategoryCollection.arrow fs)
      = record
      { elements
        = Functor.map
          (functor-list F) fs
      }

    abstract

      map-equal
        : {xs ys : Category.Object (category-collection C R)}
        → {fs₁ fs₂ : Category.Arrow (category-collection C R) xs ys}
        → Category.ArrowEqual (category-collection C R) fs₁ fs₂
        → Category.ArrowEqual (category-collection D S) (map fs₁) (map fs₂)
      map-equal (CategoryCollection.arrow-equal ps)
        = record
        { elements
          = Functor.map-equal
            (functor-list F) ps
        }

      map-identity
        : (xs : Category.Object (category-collection C R))
        → Category.ArrowEqual (category-collection D S)
          (map (Category.identity (category-collection C R) xs))
          (Category.identity (category-collection D S) (base xs))
      map-identity (collection xs _)
        = record
        { elements
          = Functor.map-identity
            (functor-list F) xs
        }

      map-compose
        : {x y z : Category.Object (category-collection C R)}
        → (f : Category.Arrow (category-collection C R) y z)
        → (g : Category.Arrow (category-collection C R) x y)
        → Category.ArrowEqual (category-collection D S)
          (map (Category.compose (category-collection C R) f g))
          (Category.compose (category-collection D S) (map f) (map g))
      map-compose (CategoryCollection.arrow fs) (CategoryCollection.arrow gs)
        = record
        { elements
          = Functor.map-compose
            (functor-list F) fs gs
        }

  functor-collection
    : (F : Functor C D)
    → FunctionInjective R S (Functor.function F)
    → Functor
      (category-collection C R)
      (category-collection D S)
  functor-collection F i
    = record {FunctorCollection F i}

-- ## Functor'

module FunctorCollection'
  (C : Category)
  (R : Relation (Category.Object C))
  where

  base
    : Category.Object (category-collection C R)
    → Category.Object (category-list C)
  base (collection xs _)
    = xs

  map
    : {x y : Category.Object (category-collection C R)}
    → Category.Arrow (category-collection C R) x y
    → Category.Arrow (category-list C) (base x) (base y)
  map (CategoryCollection.arrow fs)
    = fs

  abstract

    map-equal
      : {x y : Category.Object (category-collection C R)}
      → {f₁ f₂ : Category.Arrow (category-collection C R) x y}
      → Category.ArrowEqual (category-collection C R) f₁ f₂
      → Category.ArrowEqual (category-list C) (map f₁) (map f₂)
    map-equal (CategoryCollection.arrow-equal ps)
      = ps

    map-identity
      : (x : Category.Object (category-collection C R))
      → Category.ArrowEqual (category-list C)
        (map (Category.identity (category-collection C R) x))
        (Category.identity (category-list C) (base x))
    map-identity _
      = Category.arrow-refl (category-list C)

    map-compose
      : {x y z : Category.Object (category-collection C R)}
      → (f : Category.Arrow (category-collection C R) y z)
      → (g : Category.Arrow (category-collection C R) x y)
      → Category.ArrowEqual (category-list C)
        (map (Category.compose (category-collection C R) f g))
        (Category.compose (category-list C) (map f) (map g))
    map-compose _ _
      = Category.arrow-refl (category-list C)

functor-collection'
  : (C : Category)
  → (R : Relation (Category.Object C))
  → Functor
    (category-collection C R)
    (category-list C)
functor-collection' C R
  = record {FunctorCollection' C R}

-- ## FunctorEqual

module _
  {C D : Category}
  {R : Relation (Category.Object C)}
  {S : Relation (Category.Object D)}
  {F₁ F₂ : Functor C D}
  where

  module FunctorEqualCollection
    (i₁ : FunctionInjective R S (Functor.function F₁))
    (i₂ : FunctionInjective R S (Functor.function F₂))
    (p : FunctorEqual F₁ F₂)
    where

    base
      : (xs : Category.Object (category-collection C R))
      → Functor.base (functor-collection F₁ i₁) xs
        ≅ Functor.base (functor-collection F₂ i₂) xs
    base (collection xs _)
      = collection-equal
        (FunctorEqual.base (functor-equal-list p) xs)
  
    map
      : {xs ys : Category.Object (category-collection C R)}
      → (fs : Category.Arrow (category-collection C R) xs ys)
      → Category'.ArrowEqual'
        (category-collection D S)
        (category-collection D S)
        (Functor.map (functor-collection F₁ i₁) fs)
        (Functor.map (functor-collection F₂ i₂) fs)
    map {xs = xs} {ys = ys} (CategoryCollection.arrow fs)
      = arrow-equal-collection
        (Functor.base (functor-collection F₁ i₁) xs)
        (Functor.base (functor-collection F₂ i₂) xs)
        (Functor.base (functor-collection F₁ i₁) ys)
        (Functor.base (functor-collection F₂ i₂) ys)
        (FunctorEqual.map (functor-equal-list p) fs)

  functor-equal-collection
    : (i₁ : FunctionInjective R S (Functor.function F₁))
    → (i₂ : FunctionInjective R S (Functor.function F₂))
    → FunctorEqual F₁ F₂
    → FunctorEqual
      (functor-collection F₁ i₁)
      (functor-collection F₂ i₂)
  functor-equal-collection i₁ i₂ p
    = record {FunctorEqualCollection i₁ i₂ p}

-- ## FunctorIdentity

module _
  {C : Category}
  {R : Relation (Category.Object C)}
  {F : Functor C C}
  where

  module FunctorIdentityCollection
    (i : FunctionInjective R R (Functor.function F))
    (p : FunctorIdentity F)
    where

    base
      : (xs : Category.Object (category-collection C R))
      → Functor.base (functor-collection F i) xs ≅ xs
    base (collection xs _)
      = collection-equal
        (FunctorIdentity.base (functor-identity-list p) xs)

    map
      : {xs ys : Category.Object (category-collection C R)}
      → (fs : Category.Arrow (category-collection C R) xs ys)
      → Category'.ArrowEqual'
        (category-collection C R)
        (category-collection C R)
        (Functor.map (functor-collection F i) fs) fs
    map {xs = xs} {ys = ys} (CategoryCollection.arrow fs)
      = arrow-equal-collection
        (Functor.base F' xs) xs
        (Functor.base F' ys) ys
        (FunctorIdentity.map (functor-identity-list p) fs)
      where
        F' = functor-collection F i

  functor-identity-collection
    : (i : FunctionInjective R R (Functor.function F))
    → FunctorIdentity F
    → FunctorIdentity
      (functor-collection F i)
  functor-identity-collection i p
    = record {FunctorIdentityCollection i p}

-- ## FunctorCompose

module _
  {C D E : Category}
  {R : Relation (Category.Object C)}
  {S : Relation (Category.Object D)}
  {T : Relation (Category.Object E)}
  {F : Functor D E}
  {G : Functor C D}
  {H : Functor C E}
  where

  module FunctorComposeCollection
    (i : FunctionInjective S T (Functor.function F))
    (j : FunctionInjective R S (Functor.function G))
    (k : FunctionInjective R T (Functor.function H))
    (p : FunctorCompose F G H)
    where

    base
      : (xs : Category.Object (category-collection C R))
      → Functor.base (functor-collection H k) xs
      ≅ Functor.base (functor-collection F i)
        (Functor.base (functor-collection G j) xs)
    base (collection xs _)
      = collection-equal
        (FunctorCompose.base (functor-compose-list p) xs)

    map
      : {xs ys : Category.Object (category-collection C R)}
      → (fs : Category.Arrow (category-collection C R) xs ys)
      → Category'.ArrowEqual'
        (category-collection E T)
        (category-collection E T)
        (Functor.map (functor-collection H k) fs)
        (Functor.map (functor-collection F i)
          (Functor.map (functor-collection G j) fs))
    map {xs = xs} {ys = ys} (CategoryCollection.arrow fs)
      = arrow-equal-collection
        (Functor.base H' xs)
        (Functor.base F' (Functor.base G' xs))
        (Functor.base H' ys)
        (Functor.base F' (Functor.base G' ys))
        (FunctorCompose.map (functor-compose-list p) fs)
      where
        F' = functor-collection F i
        G' = functor-collection G j
        H' = functor-collection H k

  functor-compose-collection
    : (i : FunctionInjective S T (Functor.function F))
    → (j : FunctionInjective R S (Functor.function G))
    → (k : FunctionInjective R T (Functor.function H))
    → FunctorCompose F G H
    → FunctorCompose
      (functor-collection F i)
      (functor-collection G j)
      (functor-collection H k)
  functor-compose-collection i j k p
    = record {FunctorComposeCollection i j k p}

-- ## FunctorSquare

module _
  {C₁ C₂ D₁ D₂ : Category}
  {R₁ : Relation (Category.Object C₁)}
  {R₂ : Relation (Category.Object C₂)}
  {S₁ : Relation (Category.Object D₁)}
  {S₂ : Relation (Category.Object D₂)}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : Functor C₁ D₁}
  {H₂ : Functor C₂ D₂}
  where

  module FunctorSquareCollection
    (i : FunctionInjective R₁ R₂ (Functor.function F))
    (j : FunctionInjective S₁ S₂ (Functor.function G))
    (k₁ : FunctionInjective R₁ S₁ (Functor.function H₁))
    (k₂ : FunctionInjective R₂ S₂ (Functor.function H₂))
    (s : FunctorSquare F G H₁ H₂)
    where

    base
      : (xs₁ : Category.Object (category-collection C₁ R₁))
      → Functor.base (functor-collection H₂ k₂)
        (Functor.base (functor-collection F i) xs₁) 
      ≅ Functor.base (functor-collection G j)
        (Functor.base (functor-collection H₁ k₁) xs₁)
    base (collection xs₁ _)
      = collection-equal
        (FunctorSquare.base (functor-square-list s) xs₁)

    map
      : {xs₁ ys₁ : Category.Object (category-collection C₁ R₁)}
      → (fs₁ : Category.Arrow (category-collection C₁ R₁) xs₁ ys₁)
      → Category'.ArrowEqual'
        (category-collection D₂ S₂)
        (category-collection D₂ S₂)
        (Functor.map (functor-collection H₂ k₂)
          (Functor.map (functor-collection F i) fs₁))
        (Functor.map (functor-collection G j)
          (Functor.map (functor-collection H₁ k₁) fs₁))
    map {xs₁ = xs₁} {ys₁ = ys₁} (CategoryCollection.arrow fs₁)
      = arrow-equal-collection
        (Functor.base H₂' (Functor.base F' xs₁))
        (Functor.base G' (Functor.base H₁' xs₁))
        (Functor.base H₂' (Functor.base F' ys₁))
        (Functor.base G' (Functor.base H₁' ys₁))
        (FunctorSquare.map (functor-square-list s) fs₁)
      where
        F' = functor-collection F i
        G' = functor-collection G j
        H₁' = functor-collection H₁ k₁
        H₂' = functor-collection H₂ k₂

  functor-square-collection
    : (i : FunctionInjective R₁ R₂ (Functor.function F))
    → (j : FunctionInjective S₁ S₂ (Functor.function G))
    → (k₁ : FunctionInjective R₁ S₁ (Functor.function H₁))
    → (k₂ : FunctionInjective R₂ S₂ (Functor.function H₂))
    → FunctorSquare F G H₁ H₂
    → FunctorSquare
      (functor-collection F i)
      (functor-collection G j)
      (functor-collection H₁ k₁)
      (functor-collection H₂ k₂)
  functor-square-collection i j k₁ k₂ s
    = record {FunctorSquareCollection i j k₁ k₂ s}

-- ## FunctorSquare'

functor-square-collection'
  : {C₁ C₂ : Category}
  → {R₁ : Relation (Category.Object C₁)}
  → {R₂ : Relation (Category.Object C₂)}
  → (F : Functor C₁ C₂)
  → (i : FunctionInjective R₁ R₂ (Functor.function F))
  → FunctorSquare
    (functor-collection F i)
    (functor-list F)
    (functor-collection' C₁ R₁)
    (functor-collection' C₂ R₂)
functor-square-collection' {C₂ = C₂} _ _
  = record
  { base
    = λ _ → refl
  ; map
    = λ _ → Category.arrow-refl' (category-list C₂)
  }

