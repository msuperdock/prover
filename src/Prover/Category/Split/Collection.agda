module Prover.Category.Split.Collection where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Collection
  using (category-collection; functor-collection)
open import Prover.Category.List
  using (category-list)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Collection
  using (partial-functor-collection)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Prelude

-- ## SplitFunctor

module SplitFunctorCollection
  (C : Category)
  (R : Relation (Category.Object C))
  (d : Decidable R)
  where

  partial-functor
    : PartialFunctor
      (category-list C)
      (category-collection C R)
  partial-functor
    = partial-functor-collection C R d

  open PartialFunctor partial-functor

  functor
    : Functor
      (category-collection C R)
      (category-list C)
  functor
    = functor-collection C R

  open Functor functor using () renaming
    ( base
      to unbase
    ; map
      to unmap
    )

  base-unbase
    : (xs' : Category.Object (category-collection C R))
    → base (unbase xs') ≡ just xs'
  base-unbase
    = Collection.from-list-elements d

  map-unmap
    : {xs' ys' : Category.Object (category-collection C R)}
    → (fs' : Category.Arrow (category-collection C R) xs' ys')
    → map (base-unbase xs') (base-unbase ys') (unmap fs') ≡ fs'
  map-unmap {xs' = xs'} {ys' = ys'} _
    with Collection.from-list-eq d (Collection.elements xs') (base-unbase xs')
    | Collection.from-list-eq d (Collection.elements ys') (base-unbase ys')
  ... | refl | refl
    = refl

  normalize-arrow
    : {xs' : Category.Object (category-collection C R)}
    → (xs : Category.Object (category-list C))
    → base xs ≡ just xs'
    → Category.Arrow (category-list C) xs (unbase xs')
  normalize-arrow xs p
    with Collection.from-list-eq d xs p
  ... | refl
    = Category.identity (category-list C) xs

  normalize-valid
    : {xs' : Category.Object (category-collection C R)}
    → (xs : Category.Object (category-list C))
    → (p : base xs ≡ just xs')
    → map p (base-unbase xs') (normalize-arrow xs p)
      ≡ Category.identity (category-collection C R) xs'
  normalize-valid {xs' = xs'} xs p
    with Collection.from-list-eq d xs p
    | Collection.from-list-eq d (Collection.elements xs') (base-unbase xs')
  ... | refl | refl
    = refl

split-functor-collection
  : (C : Category)
  → (R : Relation (Category.Object C))
  → Decidable R
  → SplitFunctor
    (category-list C)
    (category-collection C R)
split-functor-collection C R d
  = record {SplitFunctorCollection C R d}

