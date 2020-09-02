module Prover.Category.Collection where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.List
  using (module CategoryList; category-list)
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

module FunctorCollection
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

functor-collection
  : (C : Category)
  → (R : Relation (Category.Object C))
  → Functor
    (category-collection C R)
    (category-list C)
functor-collection C R
  = record {FunctorCollection C R}

