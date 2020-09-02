module Prover.Category.Partial.Collection where

open import Prover.Category
  using (Category)
open import Prover.Category.Collection
  using (module CategoryCollection; category-collection)
open import Prover.Category.List
  using (category-list)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Prelude

-- ## PartialFunctor

module PartialFunctorCollection
  (C : Category)
  (R : Relation (Category.Object C))
  (d : Decidable R)
  where

  base
    : Category.Object (category-list C)
    → Maybe (Category.Object (category-collection C R))
  base
    = Collection.from-list R d

  map
    : {xs ys : Category.Object (category-list C)}
    → {xs' ys' : Category.Object (category-collection C R)}
    → base xs ≡ just xs'
    → base ys ≡ just ys'
    → Category.Arrow (category-list C) xs ys
    → Category.Arrow (category-collection C R) xs' ys'
  map {xs = xs} {ys = ys} p q
    with Collection.from-list-eq d xs p
    | Collection.from-list-eq d ys q
  ... | refl | refl
    = CategoryCollection.arrow

  abstract

    map-identity
      : {xs' : Category.Object (category-collection C R)}
      → (xs : Category.Object (category-list C))
      → (p : base xs ≡ just xs')
      → map p p (Category.identity (category-list C) xs)
        ≡ Category.identity (category-collection C R) xs'
    map-identity xs p
      with Collection.from-list-eq d xs p
    ... | refl
      = refl

    map-compose
      : {xs ys zs : Category.Object (category-list C)}
      → {xs' ys' zs' : Category.Object (category-collection C R)}
      → (p : base xs ≡ just xs')
      → (q : base ys ≡ just ys')
      → (r : base zs ≡ just zs')
      → (fs : Category.Arrow (category-list C) ys zs)
      → (gs : Category.Arrow (category-list C) xs ys)
      → map p r (Category.compose (category-list C) fs gs)
        ≡ Category.compose (category-collection C R) (map q r fs) (map p q gs)
    map-compose {xs = xs} {ys = ys} {zs = zs} p q r _ _
      with Collection.from-list-eq d xs p
      | Collection.from-list-eq d ys q
      | Collection.from-list-eq d zs r
    ... | refl | refl | refl
      = refl

partial-functor-collection
  : (C : Category)
  → (R : Relation (Category.Object C))
  → Decidable R
  → PartialFunctor
    (category-list C)
    (category-collection C R)
partial-functor-collection C R d
  = record {PartialFunctorCollection C R d}

