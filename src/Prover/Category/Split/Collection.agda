module Prover.Category.Split.Collection where

open import Prover.Category
  using (Category; Functor; FunctorSquare)
open import Prover.Category.Collection
  using (category-collection; functor-collection; functor-collection';
    functor-square-collection')
open import Prover.Category.List
  using (category-list; functor-list)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Partial.Collection
  using (partial-functor-collection; partial-functor-square-collection)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Function.Relation
  using (FunctionInjective)
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
    = functor-collection' C R

  open Functor functor using () renaming
    ( base
      to unbase
    ; map
      to unmap
    )

  base-unbase
    : (xs' : Category.Object (category-collection C R))
    → base (unbase xs') ≡ just xs'
  base-unbase (collection xs' p)
    with Collection.from-list' R d xs'
  ... | no ¬p
    = ⊥-elim (¬p p)
  ... | yes _
    = refl

  map-unmap
    : {xs' ys' : Category.Object (category-collection C R)}
    → (fs' : Category.Arrow (category-collection C R) xs' ys')
    → map (base-unbase xs') (base-unbase ys') (unmap fs') ≡ fs'
  map-unmap {xs' = collection xs' p} {ys' = collection ys' q} _
    with Collection.from-list' R d xs'
    | Collection.from-list' R d ys'
  ... | no ¬p | _
    = ⊥-elim (¬p p)
  ... | _ | no ¬q
    = ⊥-elim (¬q q)
  ... | yes _ | yes _
    = refl

  normalize-arrow
    : {xs' : Category.Object (category-collection C R)}
    → (xs : Category.Object (category-list C))
    → base xs ≡ just xs'
    → Category.Arrow (category-list C) xs (unbase xs')
  normalize-arrow xs _
    with Collection.from-list' R d xs
  normalize-arrow xs refl | yes _
    = Category.identity (category-list C) xs

  normalize-valid
    : {xs' : Category.Object (category-collection C R)}
    → (xs : Category.Object (category-list C))
    → (p : base xs ≡ just xs')
    → map p (base-unbase xs') (normalize-arrow xs p)
      ≡ Category.identity (category-collection C R) xs'
  normalize-valid {xs' = collection xs' p} xs _
    with Collection.from-list' R d xs
    | Collection.from-list' R d xs'
  ... | _ | no ¬p
    = ⊥-elim (¬p p)
  normalize-valid _ refl | yes _ | yes _
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

-- ## SplitFunctorSquare

module _
  {C₁ C₂ : Category}
  {R₁ : Relation (Category.Object C₁)}
  {R₂ : Relation (Category.Object C₂)}
  where

  module SplitFunctorSquareCollection
    (d₁ : Decidable R₁)
    (d₂ : Decidable R₂)
    (F : Functor C₁ C₂)
    (i : FunctionInjective R₁ R₂ (Functor.function F))
    where

    partial-functor
      : PartialFunctorSquare
        (functor-list F)
        (functor-collection F i)
        (SplitFunctor.partial-functor (split-functor-collection C₁ R₁ d₁))
        (SplitFunctor.partial-functor (split-functor-collection C₂ R₂ d₂))
    partial-functor
      = partial-functor-square-collection d₁ d₂ F i

    functor
      : FunctorSquare
        (functor-collection F i)
        (functor-list F)
        (SplitFunctor.functor (split-functor-collection C₁ R₁ d₁))
        (SplitFunctor.functor (split-functor-collection C₂ R₂ d₂))
    functor
      = functor-square-collection' F i

  split-functor-square-collection
    : (d₁ : Decidable R₁)
    → (d₂ : Decidable R₂)
    → (F : Functor C₁ C₂)
    → (i : FunctionInjective R₁ R₂ (Functor.function F))
    → SplitFunctorSquare
      (functor-list F)
      (functor-collection F i)
      (split-functor-collection C₁ R₁ d₁)
      (split-functor-collection C₂ R₂ d₂)
  split-functor-square-collection d₁ d₂ F i
    = record {SplitFunctorSquareCollection d₁ d₂ F i}

