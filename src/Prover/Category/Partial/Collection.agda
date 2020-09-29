module Prover.Category.Partial.Collection where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Collection
  using (category-collection; functor-collection)
open import Prover.Category.Induced
  using (module CategoryInduced)
open import Prover.Category.List
  using (category-list; functor-list)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Function.Relation
  using (FunctionInjective)
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
  map {xs = xs} {ys = ys} _ _
    with Collection.from-list' R d xs
    | Collection.from-list' R d ys
  map refl refl | yes _ | yes _
    = CategoryInduced.arrow

  abstract

    map-identity
      : {xs' : Category.Object (category-collection C R)}
      → (xs : Category.Object (category-list C))
      → (p : base xs ≡ just xs')
      → map p p (Category.identity (category-list C) xs)
        ≡ Category.identity (category-collection C R) xs'
    map-identity xs _
      with Collection.from-list' R d xs
    map-identity _ refl | yes _
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
    map-compose {xs = xs} {ys = ys} {zs = zs} _ _ _ _ _
      with Collection.from-list' R d xs
      | Collection.from-list' R d ys
      | Collection.from-list' R d zs
    map-compose refl refl refl _ _ | yes _ | yes _ | yes _
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

-- ## PartialFunctorSquare

module _
  {C₁ C₂ : Category}
  {R₁ : Relation (Category.Object C₁)}
  {R₂ : Relation (Category.Object C₂)}
  where

  module PartialFunctorSquareCollection
    (d₁ : Decidable R₁)
    (d₂ : Decidable R₂)
    (F : Functor C₁ C₂)
    (i : FunctionInjective R₁ R₂ (Functor.function F))
    where

    base
      : {xs₁' : Category.Object (category-collection C₁ R₁)}
      → (xs₁ : Category.Object (category-list C₁))
      → PartialFunctor.base (partial-functor-collection C₁ R₁ d₁) xs₁
        ≡ just xs₁'
      → PartialFunctor.base (partial-functor-collection C₂ R₂ d₂)
        (Functor.base (functor-list F) xs₁)
      ≡ just (Functor.base (functor-collection F i) xs₁')
    base xs₁ _
      with Collection.from-list' R₁ d₁ xs₁
      | Collection.from-list' R₂ d₂ (List.map (Functor.base F) xs₁)
    base {xs₁' = xs₁'} _ refl | yes _ | no ¬p₂
      = ⊥-elim (¬p₂ (Collection.valid'
        (Collection.map R₂ (Functor.base F) (FunctionInjective.base i) xs₁')))
    base _ refl | yes _ | yes _
      = refl

    map
      : {xs₁ ys₁ : Category.Object (category-list C₁)}
      → {xs₁' ys₁' : Category.Object (category-collection C₁ R₁)}
      → (p₁ : PartialFunctor.base (partial-functor-collection C₁ R₁ d₁) xs₁
        ≡ just xs₁')
      → (q₁ : PartialFunctor.base (partial-functor-collection C₁ R₁ d₁) ys₁
        ≡ just ys₁')
      → (fs₁ : Category.Arrow (category-list C₁) xs₁ ys₁)
      → PartialFunctor.map (partial-functor-collection C₂ R₂ d₂)
        (base xs₁ p₁)
        (base ys₁ q₁)
        (Functor.map (functor-list F) fs₁)
      ≡ Functor.map (functor-collection F i)
        (PartialFunctor.map (partial-functor-collection C₁ R₁ d₁) p₁ q₁ fs₁)
    map {xs₁ = xs₁} {ys₁ = ys₁} _ _ _
      with Collection.from-list' R₁ d₁ xs₁
      | Collection.from-list' R₂ d₂ (List.map (Functor.base F) xs₁)
      | Collection.from-list' R₁ d₁ ys₁
      | Collection.from-list' R₂ d₂ (List.map (Functor.base F) ys₁)
    map {xs₁' = xs₁'} refl _ _ | yes _ | no ¬p₂ | _ | _
      = ⊥-elim (¬p₂ (Collection.valid'
        (Collection.map R₂ (Functor.base F) (FunctionInjective.base i) xs₁')))
    map {ys₁' = ys₁'} _ refl _ | _ | _ | yes _ | no ¬q₂
      = ⊥-elim (¬q₂ (Collection.valid'
        (Collection.map R₂ (Functor.base F) (FunctionInjective.base i) ys₁')))
    map refl refl _ | yes _ | yes _ | yes _ | yes _
      = refl

  partial-functor-square-collection
    : (d₁ : Decidable R₁)
    → (d₂ : Decidable R₂)
    → (F : Functor C₁ C₂)
    → (i : FunctionInjective R₁ R₂ (Functor.function F))
    → PartialFunctorSquare
      (functor-list F)
      (functor-collection F i)
      (partial-functor-collection C₁ R₁ d₁)
      (partial-functor-collection C₂ R₂ d₂)
  partial-functor-square-collection d₁ d₂ F i
    = record {PartialFunctorSquareCollection d₁ d₂ F i}

