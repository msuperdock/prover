module Prover.Category.Collection where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.List
  using (module CategoryList; category-list; functor-compose-list;
    functor-identity-list; functor-list; functor-square-list)
open import Prover.Prelude

-- ## Category

module CategoryCollection
  (C : Category)
  (R : Relation (Category.Object C))
  where

  Object
    : Set
  Object
    = Collection R

  record Arrow
    (xs : Object)
    (ys : Object)
    : Set
    where

    constructor
    
      arrow

    field
      
      elements
        : CategoryList.Arrow C
          (Collection.elements xs)
          (Collection.elements ys)

  arrow-eq
    : {xs₁ xs₂ ys₁ ys₂ : Object}
    → {fs₁ : Arrow xs₁ ys₁}
    → {fs₂ : Arrow xs₂ ys₂}
    → xs₁ ≡ xs₂
    → ys₁ ≡ ys₂
    → Arrow.elements fs₁ ≅ Arrow.elements fs₂
    → fs₁ ≅ fs₂
  arrow-eq refl refl refl
    = refl

  identity
    : (xs : Object)
    → Arrow xs xs
  identity (collection xs _)
    = arrow
    $ Category.identity
      (category-list C) xs

  compose
    : {xs ys zs : Object}
    → Arrow ys zs
    → Arrow xs ys
    → Arrow xs zs
  compose (arrow fs) (arrow gs)
    = arrow
    $ Category.compose
      (category-list C) fs gs

  abstract

    precompose
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → compose fs (identity xs) ≡ fs
    precompose (arrow fs)
      = sub arrow
      $ Category.precompose
        (category-list C) fs

    postcompose
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → compose (identity ys) fs ≡ fs
    postcompose (arrow fs)
      = sub arrow
      $ Category.postcompose
        (category-list C) fs

    associative
      : {ws xs ys zs : Object}
      → (fs : Arrow ys zs)
      → (gs : Arrow xs ys)
      → (hs : Arrow ws xs)
      → compose (compose fs gs) hs ≡ compose fs (compose gs hs)
    associative (arrow fs) (arrow gs) (arrow hs)
      = sub arrow
      $ Category.associative
        (category-list C) fs gs hs

category-collection
  : (C : Category)
  → Relation (Category.Object C)
  → Category
category-collection C R
  = record {CategoryCollection C R}

-- ## Functor

module _
  {C D : Category}
  where

  module FunctorCollection
    (R : Relation (Category.Object C))
    (S : Relation (Category.Object D))
    (F : Functor C D)
    (i : Injective R S (Functor.base F))
    where

    base
      : Category.Object (category-collection C R)
      → Category.Object (category-collection D S)
    base
      = Collection.map S (Functor.base F) i

    map
      : {xs ys : Category.Object (category-collection C R)}
      → Category.Arrow (category-collection C R) xs ys
      → Category.Arrow (category-collection D S) (base xs) (base ys)
    map (CategoryCollection.arrow xs)
      = CategoryCollection.arrow
      $ Functor.map
        (functor-list F) xs

    abstract

      map-identity
        : (xs : Category.Object (category-collection C R))
        → map (Category.identity (category-collection C R) xs)
          ≡ Category.identity (category-collection D S) (base xs)
      map-identity (collection xs _)
        = sub CategoryCollection.arrow
        $ Functor.map-identity
          (functor-list F) xs

      map-compose
        : {xs ys zs : Category.Object (category-collection C R)}
        → (fs : Category.Arrow (category-collection C R) ys zs)
        → (gs : Category.Arrow (category-collection C R) xs ys)
        → map (Category.compose (category-collection C R) fs gs)
          ≡ Category.compose (category-collection D S) (map fs) (map gs)
      map-compose (CategoryCollection.arrow fs) (CategoryCollection.arrow gs)
        = sub CategoryCollection.arrow
        $ Functor.map-compose (functor-list F) fs gs

  functor-collection
    : (R : Relation (Category.Object C))
    → (S : Relation (Category.Object D))
    → (F : Functor C D)
    → Injective R S (Functor.base F)
    → Functor
      (category-collection C R)
      (category-collection D S)
  functor-collection R S F i
    = record {FunctorCollection R S F i}

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
    : {xs ys : Category.Object (category-collection C R)}
    → Category.Arrow (category-collection C R) xs ys
    → Category.Arrow (category-list C) (base xs) (base ys)
  map (CategoryCollection.arrow fs)
    = fs

  abstract

    map-identity
      : (xs : Category.Object (category-collection C R))
      → map (Category.identity (category-collection C R) xs)
        ≡ Category.identity (category-list C) (base xs)
    map-identity _
      = refl

    map-compose
      : {xs ys zs : Category.Object (category-collection C R)}
      → (fs : Category.Arrow (category-collection C R) ys zs)
      → (gs : Category.Arrow (category-collection C R) xs ys)
      → map (Category.compose (category-collection C R) fs gs)
        ≡ Category.compose (category-list C) (map fs) (map gs)
    map-compose _ _
      = refl

functor-collection'
  : (C : Category)
  → (R : Relation (Category.Object C))
  → Functor
    (category-collection C R)
    (category-list C)
functor-collection' C R
  = record {FunctorCollection' C R}

-- ## FunctorIdentity

module FunctorIdentityCollection
  {C : Category}
  (R : Relation (Category.Object C))
  {F : Functor C C}
  (i : Injective R R (Functor.base F))
  (p : FunctorIdentity F)
  where

  base
    : (xs : Category.Object (category-collection C R))
    → Functor.base (functor-collection R R F i) xs ≅ xs
  base (collection xs _)
    = collection-eq
    $ FunctorIdentity.base
      (functor-identity-list p) xs

  map
    : {xs ys : Category.Object (category-collection C R)}
    → (fs : Category.Arrow (category-collection C R) xs ys)
    → Functor.map (functor-collection R R F i) fs ≅ fs
  map {xs = xs} {ys = ys} (CategoryCollection.arrow fs)
    = CategoryCollection.arrow-eq C R (base xs) (base ys)
    $ FunctorIdentity.map
      (functor-identity-list p) fs

functor-identity-collection
  : {C : Category}
  → (R : Relation (Category.Object C))
  → {F : Functor C C}
  → (i : Injective R R (Functor.base F))
  → FunctorIdentity F
  → FunctorIdentity
    (functor-collection R R F i)
functor-identity-collection R i p
  = record {FunctorIdentityCollection R i p}

-- ## FunctorCompose

module FunctorComposeCollection
  {C D E : Category}
  (R : Relation (Category.Object C))
  (S : Relation (Category.Object D))
  (T : Relation (Category.Object E))
  {F : Functor D E}
  {G : Functor C D}
  {H : Functor C E}
  (i : Injective S T (Functor.base F))
  (j : Injective R S (Functor.base G))
  (k : Injective R T (Functor.base H))
  (p : FunctorCompose F G H)
  where

  base
    : (xs : Category.Object (category-collection C R))
    → Functor.base (functor-collection R T H k) xs
    ≅ Functor.base (functor-collection S T F i)
      (Functor.base (functor-collection R S G j) xs)
  base (collection xs _)
    = collection-eq
    $ FunctorCompose.base
      (functor-compose-list p) xs

  map
    : {xs ys : Category.Object (category-collection C R)}
    → (fs : Category.Arrow (category-collection C R) xs ys)
    → Functor.map (functor-collection R T H k) fs
    ≅ Functor.map (functor-collection S T F i)
      (Functor.map (functor-collection R S G j) fs)
  map {xs = xs} {ys = ys} (CategoryCollection.arrow fs)
    = CategoryCollection.arrow-eq E T (base xs) (base ys)
    $ FunctorCompose.map
      (functor-compose-list p) fs

functor-compose-collection
  : {C D E : Category}
  → (R : Relation (Category.Object C))
  → (S : Relation (Category.Object D))
  → (T : Relation (Category.Object E))
  → {F : Functor D E}
  → {G : Functor C D}
  → {H : Functor C E}
  → (i : Injective S T (Functor.base F))
  → (j : Injective R S (Functor.base G))
  → (k : Injective R T (Functor.base H))
  → FunctorCompose F G H
  → FunctorCompose
    (functor-collection S T F i)
    (functor-collection R S G j)
    (functor-collection R T H k)
functor-compose-collection R S T i j k p
  = record {FunctorComposeCollection R S T i j k p}

-- ## FunctorSquare

module FunctorSquareCollection
  {C₁ C₂ D₁ D₂ : Category}
  (R₁ : Relation (Category.Object C₁))
  (R₂ : Relation (Category.Object C₂))
  (S₁ : Relation (Category.Object D₁))
  (S₂ : Relation (Category.Object D₂))
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : Functor C₁ D₁}
  {H₂ : Functor C₂ D₂}
  (i : Injective R₁ R₂ (Functor.base F))
  (j : Injective S₁ S₂ (Functor.base G))
  (k₁ : Injective R₁ S₁ (Functor.base H₁))
  (k₂ : Injective R₂ S₂ (Functor.base H₂))
  (s : FunctorSquare F G H₁ H₂)
  where

  base
    : (xs₁ : Category.Object (category-collection C₁ R₁))
    → Functor.base (functor-collection R₂ S₂ H₂ k₂)
      (Functor.base (functor-collection R₁ R₂ F i) xs₁) 
    ≅ Functor.base (functor-collection S₁ S₂ G j)
      (Functor.base (functor-collection R₁ S₁ H₁ k₁) xs₁)
  base (collection xs₁ _)
    = collection-eq
    $ FunctorSquare.base
      (functor-square-list s) xs₁

  map
    : {xs₁ ys₁ : Category.Object (category-collection C₁ R₁)}
    → (fs₁ : Category.Arrow (category-collection C₁ R₁) xs₁ ys₁)
    → Functor.map (functor-collection R₂ S₂ H₂ k₂)
      (Functor.map (functor-collection R₁ R₂ F i) fs₁)
    ≅ Functor.map (functor-collection S₁ S₂ G j)
      (Functor.map (functor-collection R₁ S₁ H₁ k₁) fs₁)
  map {xs₁ = xs₁} {ys₁ = ys₁} (CategoryCollection.arrow fs₁)
    = CategoryCollection.arrow-eq D₂ S₂ (base xs₁) (base ys₁)
    $ FunctorSquare.map
      (functor-square-list s) fs₁

functor-square-collection
  : {C₁ C₂ D₁ D₂ : Category}
  → (R₁ : Relation (Category.Object C₁))
  → (R₂ : Relation (Category.Object C₂))
  → (S₁ : Relation (Category.Object D₁))
  → (S₂ : Relation (Category.Object D₂))
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → (i : Injective R₁ R₂ (Functor.base F))
  → (j : Injective S₁ S₂ (Functor.base G))
  → (k₁ : Injective R₁ S₁ (Functor.base H₁))
  → (k₂ : Injective R₂ S₂ (Functor.base H₂))
  → FunctorSquare F G H₁ H₂
  → FunctorSquare
    (functor-collection R₁ R₂ F i)
    (functor-collection S₁ S₂ G j)
    (functor-collection R₁ S₁ H₁ k₁)
    (functor-collection R₂ S₂ H₂ k₂)
functor-square-collection R₁ R₂ S₁ S₂ i j k₁ k₂ s
  = record {FunctorSquareCollection R₁ R₂ S₁ S₂ i j k₁ k₂ s}

-- ## FunctorSquare'

module FunctorSquareCollection'
  {C₁ C₂ : Category}
  (R₁ : Relation (Category.Object C₁))
  (R₂ : Relation (Category.Object C₂))
  (F : Functor C₁ C₂)
  (i : Injective R₁ R₂ (Functor.base F))
  where

  base
    : (xs₁ : Category.Object (category-collection C₁ R₁))
    → Functor.base (functor-collection' C₂ R₂)
      (Functor.base (functor-collection R₁ R₂ F i) xs₁) 
    ≅ Functor.base (functor-list F)
      (Functor.base (functor-collection' C₁ R₁) xs₁)
  base _
    = refl

  map
    : {xs₁ ys₁ : Category.Object (category-collection C₁ R₁)}
    → (fs₁ : Category.Arrow (category-collection C₁ R₁) xs₁ ys₁)
    → Functor.map (functor-collection' C₂ R₂)
      (Functor.map (functor-collection R₁ R₂ F i) fs₁)
    ≅ Functor.map (functor-list F)
      (Functor.map (functor-collection' C₁ R₁) fs₁)
  map _
    = refl

functor-square-collection'
  : {C₁ C₂ : Category}
  → (R₁ : Relation (Category.Object C₁))
  → (R₂ : Relation (Category.Object C₂))
  → (F : Functor C₁ C₂)
  → (i : Injective R₁ R₂ (Functor.base F))
  → FunctorSquare
    (functor-collection R₁ R₂ F i)
    (functor-list F)
    (functor-collection' C₁ R₁)
    (functor-collection' C₂ R₂)
functor-square-collection' R₁ R₂ F i
  = record {FunctorSquareCollection' R₁ R₂ F i}

