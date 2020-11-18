module Prover.Category.Collection.Unit where

open import Prover.Category
  using (module Category'; Category; Functor; FunctorCompose; FunctorEqual;
    FunctorIdentity; FunctorSquare)
open import Prover.Category.List.Unit
  using (module CategoryListUnit; module FunctorListUnit; category-list-unit;
    functor-compose-list-unit; functor-equal-list-unit;
    functor-identity-list-unit; functor-list-unit; functor-square-list-unit)
open import Prover.Function
  using (Function; FunctionCompose; FunctionEqual; FunctionIdentity;
    FunctionSquare)
open import Prover.Function.Relation
  using (FunctionInjective)
open import Prover.Prelude

-- ## Category

-- ### Function

module _
  {A : Set}
  where

  module CategoryCollectionUnit
    (R : Relation A)
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
          : CategoryListUnit.Arrow
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
          : CategoryListUnit.ArrowEqual
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
          = CategoryListUnit.arrow-refl
        }

      arrow-sym
        : {xs ys : Object}
        → {fs₁ fs₂ : Arrow xs ys}
        → ArrowEqual fs₁ fs₂
        → ArrowEqual fs₂ fs₁
      arrow-sym (arrow-equal ps)
        = record
        { elements
          = CategoryListUnit.arrow-sym ps
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
          = CategoryListUnit.arrow-trans ps₁ ps₂
        }

      simplify
        : {xs ys : Object}
        → Arrow xs ys
        → Arrow xs ys
      simplify (arrow fs)
        = record
        { elements
          = CategoryListUnit.simplify fs
        }

      simplify-equal
        : {xs ys : Object}
        → (fs : Arrow xs ys)
        → ArrowEqual
          (simplify fs) fs
      simplify-equal (arrow fs)
        = record
        { elements
          = CategoryListUnit.simplify-equal fs
        }

    identity
      : (xs : Object)
      → Arrow xs xs
    identity (collection xs _)
      = record
      { elements
        = CategoryListUnit.identity xs
      }

    compose
      : {xs ys zs : Object}
      → Arrow ys zs
      → Arrow xs ys
      → Arrow xs zs
    compose (arrow fs) (arrow gs)
      = record
      { elements
        = CategoryListUnit.compose fs gs
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
          = CategoryListUnit.compose-equal ps qs
        }

      precompose
        : {xs ys : Object}
        → (fs : Arrow xs ys)
        → ArrowEqual
          (compose fs (identity xs)) fs
      precompose (arrow fs)
        = record
        { elements
          = CategoryListUnit.precompose fs
        }

      postcompose
        : {xs ys : Object}
        → (fs : Arrow xs ys)
        → ArrowEqual
          (compose (identity ys) fs) fs
      postcompose (arrow fs)
        = record
        { elements
          = CategoryListUnit.postcompose fs
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
          = CategoryListUnit.associative fs gs hs
        }

  category-collection-unit
    : Relation A
    → Category
  category-collection-unit R
    = record {CategoryCollectionUnit R}

-- ### Equality

arrow-equal-collection-unit
  : {A : Set}
  → {R : Relation A}
  → (xs₁ xs₂ ys₁ ys₂ : Collection R)
  → {fs₁ : Category.Arrow
    (category-list-unit A)
    (Collection.elements xs₁)
    (Collection.elements ys₁)}
  → {fs₂ : Category.Arrow
    (category-list-unit A)
    (Collection.elements xs₂)
    (Collection.elements ys₂)}
  → Category.ArrowEqual' (category-list-unit A) fs₁ fs₂
  → Category.ArrowEqual'
    (category-collection-unit R)
    (CategoryCollectionUnit.arrow {xs = xs₁} {ys = ys₁} fs₁)
    (CategoryCollectionUnit.arrow {xs = xs₂} {ys = ys₂} fs₂)
arrow-equal-collection-unit _ _ _ _ (Category.any p)
  = Category.any
  $ record
  { elements
    = p
  }

-- ## Functor

module _
  {A B : Set}
  {R : Relation A}
  {S : Relation B}
  {F : Function A B}
  where

  module FunctorCollectionUnit
    (i : FunctionInjective R S F)
    where

    base
      : Category.Object (category-collection-unit R)
      → Category.Object (category-collection-unit S)
    base
      = Collection.map S
        (Function.base F)
        (FunctionInjective.base i)

    map
      : {xs ys : Category.Object (category-collection-unit R)}
      → Category.Arrow (category-collection-unit R) xs ys
      → Category.Arrow (category-collection-unit S) (base xs) (base ys)
    map (CategoryCollectionUnit.arrow fs)
      = record
      { elements
        = FunctorListUnit.map F fs
      }

    abstract

      map-equal
        : {xs ys : Category.Object (category-collection-unit R)}
        → {fs₁ fs₂ : Category.Arrow (category-collection-unit R) xs ys}
        → Category.ArrowEqual (category-collection-unit R) fs₁ fs₂
        → Category.ArrowEqual (category-collection-unit S) (map fs₁) (map fs₂)
      map-equal (CategoryCollectionUnit.arrow-equal ps)
        = record
        { elements
          = FunctorListUnit.map-equal F ps
        }

      map-identity
        : (xs : Category.Object (category-collection-unit R))
        → Category.ArrowEqual (category-collection-unit S)
          (map (Category.identity (category-collection-unit R) xs))
          (Category.identity (category-collection-unit S) (base xs))
      map-identity (collection xs _)
        = record
        { elements
          = FunctorListUnit.map-identity F xs
        }

      map-compose
        : {xs ys zs : Category.Object (category-collection-unit R)}
        → (fs : Category.Arrow (category-collection-unit R) ys zs)
        → (gs : Category.Arrow (category-collection-unit R) xs ys)
        → Category.ArrowEqual (category-collection-unit S)
          (map (Category.compose (category-collection-unit R) fs gs))
          (Category.compose (category-collection-unit S) (map fs) (map gs))
      map-compose
        (CategoryCollectionUnit.arrow fs)
        (CategoryCollectionUnit.arrow gs)
        = record
        { elements
          = FunctorListUnit.map-compose F fs gs
        }

  functor-collection-unit
    : FunctionInjective R S F
    → Functor
      (category-collection-unit R)
      (category-collection-unit S)
  functor-collection-unit i
    = record {FunctorCollectionUnit i}

-- ## Functor'

module _
  {A : Set}
  where

  module FunctorCollectionUnit'
    (R : Relation A)
    where

    base
      : Category.Object (category-collection-unit R)
      → Category.Object (category-list-unit A)
    base (collection xs _)
      = xs

    map
      : {xs ys : Category.Object (category-collection-unit R)}
      → Category.Arrow (category-collection-unit R) xs ys
      → Category.Arrow (category-list-unit A) (base xs) (base ys)
    map (CategoryCollectionUnit.arrow fs)
      = fs

    abstract

      map-equal
        : {xs ys : Category.Object (category-collection-unit R)}
        → {fs₁ fs₂ : Category.Arrow (category-collection-unit R) xs ys}
        → Category.ArrowEqual (category-collection-unit R) fs₁ fs₂
        → Category.ArrowEqual (category-list-unit A) (map fs₁) (map fs₂)
      map-equal (CategoryCollectionUnit.arrow-equal ps)
        = ps

      map-identity
        : (xs : Category.Object (category-collection-unit R))
        → Category.ArrowEqual (category-list-unit A)
          (map (Category.identity (category-collection-unit R) xs))
          (Category.identity (category-list-unit A) (base xs))
      map-identity _
        = Category.arrow-refl (category-list-unit A)

      map-compose
        : {xs ys zs : Category.Object (category-collection-unit R)}
        → (fs : Category.Arrow (category-collection-unit R) ys zs)
        → (gs : Category.Arrow (category-collection-unit R) xs ys)
        → Category.ArrowEqual (category-list-unit A)
          (map (Category.compose (category-collection-unit R) fs gs))
          (Category.compose (category-list-unit A) (map fs) (map gs))
      map-compose _ _
        = Category.arrow-refl (category-list-unit A)

  functor-collection-unit'
    : (R : Relation A)
    → Functor
      (category-collection-unit R)
      (category-list-unit A)
  functor-collection-unit' R
    = record {FunctorCollectionUnit' R}

-- ## FunctorEqual

module _
  {A B : Set}
  {R : Relation A}
  {S : Relation B}
  {F₁ F₂ : Function A B}
  where

  module FunctorEqualCollectionUnit
    (i₁ : FunctionInjective R S F₁)
    (i₂ : FunctionInjective R S F₂)
    (p : FunctionEqual F₁ F₂)
    where

    base
      : (xs : Category.Object (category-collection-unit R))
      → Functor.base (functor-collection-unit i₁) xs
        ≅ Functor.base (functor-collection-unit i₂) xs
    base (collection xs _)
      = collection-equal
        (FunctorEqual.base (functor-equal-list-unit p) xs)
  
    map
      : {xs ys : Category.Object (category-collection-unit R)}
      → (fs : Category.Arrow (category-collection-unit R) xs ys)
      → Category'.ArrowEqual'
        (category-collection-unit S)
        (category-collection-unit S)
        (Functor.map (functor-collection-unit i₁) fs)
        (Functor.map (functor-collection-unit i₂) fs)
    map {xs = xs} {ys = ys} (CategoryCollectionUnit.arrow fs)
      = arrow-equal-collection-unit
        (Functor.base (functor-collection-unit i₁) xs)
        (Functor.base (functor-collection-unit i₂) xs)
        (Functor.base (functor-collection-unit i₁) ys)
        (Functor.base (functor-collection-unit i₂) ys)
        (FunctorEqual.map (functor-equal-list-unit p) fs)

  functor-equal-collection-unit
    : (i₁ : FunctionInjective R S F₁)
    → (i₂ : FunctionInjective R S F₂)
    → FunctionEqual F₁ F₂
    → FunctorEqual
      (functor-collection-unit i₁)
      (functor-collection-unit i₂)
  functor-equal-collection-unit i₁ i₂ p
    = record {FunctorEqualCollectionUnit i₁ i₂ p}

-- ## FunctorIdentity

module _
  {A : Set}
  {R : Relation A}
  {F : Function A A}
  where

  module FunctorIdentityCollectionUnit
    (i : FunctionInjective R R F)
    (p : FunctionIdentity F)
    where

    base
      : (xs : Category.Object (category-collection-unit R))
      → Functor.base (functor-collection-unit i) xs ≅ xs
    base (collection xs _)
      = collection-equal
        (FunctorIdentity.base (functor-identity-list-unit p) xs)

    map
      : {xs ys : Category.Object (category-collection-unit R)}
      → (fs : Category.Arrow (category-collection-unit R) xs ys)
      → Category'.ArrowEqual'
        (category-collection-unit R)
        (category-collection-unit R)
        (Functor.map (functor-collection-unit i) fs) fs
    map {xs = xs} {ys = ys} (CategoryCollectionUnit.arrow fs)
      = arrow-equal-collection-unit
        (Functor.base F' xs) xs
        (Functor.base F' ys) ys
        (FunctorIdentity.map (functor-identity-list-unit p) fs)
      where
        F' = functor-collection-unit i

  functor-identity-collection-unit
    : (i : FunctionInjective R R F)
    → FunctionIdentity F
    → FunctorIdentity
      (functor-collection-unit i)
  functor-identity-collection-unit i p
    = record {FunctorIdentityCollectionUnit i p}

-- ## FunctorCompose

module _
  {A B C : Set}
  {R : Relation A}
  {S : Relation B}
  {T : Relation C}
  {F : Function B C}
  {G : Function A B}
  {H : Function A C}
  where

  module FunctorComposeCollectionUnit
    (i : FunctionInjective S T F)
    (j : FunctionInjective R S G)
    (k : FunctionInjective R T H)
    (p : FunctionCompose F G H)
    where

    base
      : (xs : Category.Object (category-collection-unit R))
      → Functor.base (functor-collection-unit k) xs
      ≅ Functor.base (functor-collection-unit i)
        (Functor.base (functor-collection-unit j) xs)
    base (collection xs _)
      = collection-equal
        (FunctorCompose.base (functor-compose-list-unit p) xs)

    map
      : {xs ys : Category.Object (category-collection-unit R)}
      → (fs : Category.Arrow (category-collection-unit R) xs ys)
      → Category'.ArrowEqual'
        (category-collection-unit T)
        (category-collection-unit T)
        (Functor.map (functor-collection-unit k) fs)
        (Functor.map (functor-collection-unit i)
          (Functor.map (functor-collection-unit j) fs))
    map {xs = xs} {ys = ys} (CategoryCollectionUnit.arrow fs)
      = arrow-equal-collection-unit
        (Functor.base H' xs)
        (Functor.base F' (Functor.base G' xs))
        (Functor.base H' ys)
        (Functor.base F' (Functor.base G' ys))
        (FunctorCompose.map (functor-compose-list-unit p) fs)
      where
        F' = functor-collection-unit i
        G' = functor-collection-unit j
        H' = functor-collection-unit k

  functor-compose-collection-unit
    : (i : FunctionInjective S T F)
    → (j : FunctionInjective R S G)
    → (k : FunctionInjective R T H)
    → FunctionCompose F G H
    → FunctorCompose
      (functor-collection-unit i)
      (functor-collection-unit j)
      (functor-collection-unit k)
  functor-compose-collection-unit i j k p
    = record {FunctorComposeCollectionUnit i j k p}

-- ## FunctorSquare

module _
  {A₁ A₂ B₁ B₂ : Set}
  {R₁ : Relation A₁}
  {R₂ : Relation A₂}
  {S₁ : Relation B₁}
  {S₂ : Relation B₂}
  {F : Function A₁ A₂}
  {G : Function B₁ B₂}
  {H₁ : Function A₁ B₁}
  {H₂ : Function A₂ B₂}
  where

  module FunctorSquareCollectionUnit
    (i : FunctionInjective R₁ R₂ F)
    (j : FunctionInjective S₁ S₂ G)
    (k₁ : FunctionInjective R₁ S₁ H₁)
    (k₂ : FunctionInjective R₂ S₂ H₂)
    (s : FunctionSquare F G H₁ H₂)
    where

    base
      : (xs₁ : Category.Object (category-collection-unit R₁))
      → Functor.base (functor-collection-unit k₂)
        (Functor.base (functor-collection-unit i) xs₁) 
      ≅ Functor.base (functor-collection-unit j)
        (Functor.base (functor-collection-unit k₁) xs₁)
    base (collection xs₁ _)
      = collection-equal
        (FunctorSquare.base (functor-square-list-unit s) xs₁)

    map
      : {xs₁ ys₁ : Category.Object (category-collection-unit R₁)}
      → (fs₁ : Category.Arrow (category-collection-unit R₁) xs₁ ys₁)
      → Category'.ArrowEqual'
        (category-collection-unit S₂)
        (category-collection-unit S₂)
        (Functor.map (functor-collection-unit k₂)
          (Functor.map (functor-collection-unit i) fs₁))
        (Functor.map (functor-collection-unit j)
          (Functor.map (functor-collection-unit k₁) fs₁))
    map {xs₁ = xs₁} {ys₁ = ys₁} (CategoryCollectionUnit.arrow fs₁)
      = arrow-equal-collection-unit
        (Functor.base H₂' (Functor.base F' xs₁))
        (Functor.base G' (Functor.base H₁' xs₁))
        (Functor.base H₂' (Functor.base F' ys₁))
        (Functor.base G' (Functor.base H₁' ys₁))
        (FunctorSquare.map (functor-square-list-unit s) fs₁)
      where
        F' = functor-collection-unit i
        G' = functor-collection-unit j
        H₁' = functor-collection-unit k₁
        H₂' = functor-collection-unit k₂

  functor-square-collection-unit
    : (i : FunctionInjective R₁ R₂ F)
    → (j : FunctionInjective S₁ S₂ G)
    → (k₁ : FunctionInjective R₁ S₁ H₁)
    → (k₂ : FunctionInjective R₂ S₂ H₂)
    → FunctionSquare F G H₁ H₂
    → FunctorSquare
      (functor-collection-unit i)
      (functor-collection-unit j)
      (functor-collection-unit k₁)
      (functor-collection-unit k₂)
  functor-square-collection-unit i j k₁ k₂ s
    = record {FunctorSquareCollectionUnit i j k₁ k₂ s}

-- ## FunctorSquare'

functor-square-collection-unit'
  : {A₁ A₂ : Set}
  → {R₁ : Relation A₁}
  → {R₂ : Relation A₂}
  → {F : Function A₁ A₂}
  → (i : FunctionInjective R₁ R₂ F)
  → FunctorSquare
    (functor-collection-unit i)
    (functor-list-unit F)
    (functor-collection-unit' R₁)
    (functor-collection-unit' R₂)
functor-square-collection-unit' {A₂ = A₂} _
  = record
  { base
    = λ _ → refl
  ; map
    = λ _ → Category.arrow-refl' (category-list-unit A₂)
  }

