module Prover.Category.Split.Collection.Unit where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Collection.Unit
  using (category-collection-unit; functor-collection-unit;
    functor-collection-unit'; functor-square-collection-unit')
open import Prover.Category.List.Unit
  using (category-list-unit; functor-list-unit)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.Collection.Unit
  using (partial-functor-collection-unit;
    partial-functor-square-collection-unit)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Function
  using (Function)
open import Prover.Function.Relation
  using (FunctionInjective)
open import Prover.Prelude

-- ## SplitFunctor

module _
  {A : Set}
  where

  module SplitFunctorCollectionUnit
    (R : Relation A)
    (d : Decidable R)
    where

    partial-functor
      : PartialFunctor
        (category-list-unit A)
        (category-collection-unit R)
    partial-functor
      = partial-functor-collection-unit R d

    open PartialFunctor partial-functor

    functor
      : Functor
        (category-collection-unit R)
        (category-list-unit A)
    functor
      = functor-collection-unit' R

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase
        : (xs : Category.Object (category-collection-unit R))
        → base (unbase xs) ≡ just xs
      base-unbase (collection xs p)
        with Collection.from-list' R d xs
      ... | no ¬p
        = ⊥-elim (¬p p)
      ... | yes _
        = refl

      map-unmap
        : {xs ys : Category.Object (category-collection-unit R)}
        → (fs : Category.Arrow (category-collection-unit R) xs ys)
        → Category.ArrowEqual
          (category-collection-unit R)
          (map (base-unbase xs) (base-unbase ys) (unmap fs)) fs
      map-unmap {xs = collection xs p} {ys = collection ys q} _
        with Collection.from-list' R d xs
        | Collection.from-list' R d ys
      ... | no ¬p | _
        = ⊥-elim (¬p p)
      ... | _ | no ¬q
        = ⊥-elim (¬q q)
      ... | yes _ | yes _
        = Category.arrow-refl (category-collection-unit R)

      normalize-arrow
        : {xs' : Category.Object (category-collection-unit R)}
        → (xs : Category.Object (category-list-unit A))
        → base xs ≡ just xs'
        → Category.Arrow (category-list-unit A) xs (unbase xs')
      normalize-arrow xs _
        with Collection.from-list' R d xs
      normalize-arrow xs refl | yes _
        = Category.identity (category-list-unit A) xs

      normalize-valid
        : {xs' : Category.Object (category-collection-unit R)}
        → (xs : Category.Object (category-list-unit A))
        → (p : base xs ≡ just xs')
        → Category.ArrowEqual
          (category-collection-unit R)
          (map p (base-unbase xs') (normalize-arrow xs p))
          (Category.identity (category-collection-unit R) xs')
      normalize-valid {xs' = collection xs' p} xs _
        with Collection.from-list' R d xs
        | Collection.from-list' R d xs'
      ... | _ | no ¬p
        = ⊥-elim (¬p p)
      normalize-valid _ refl | yes _ | yes _
        = Category.arrow-refl (category-collection-unit R)

  split-functor-collection-unit
    : (R : Relation A)
    → Decidable R
    → SplitFunctor
      (category-list-unit A)
      (category-collection-unit R)
  split-functor-collection-unit R d
    = record {SplitFunctorCollectionUnit R d}

-- ## SplitFunctorSquare

split-functor-square-collection-unit
  : {A₁ A₂ : Set}
  → {R₁ : Relation A₁}
  → {R₂ : Relation A₂}
  → (d₁ : Decidable R₁)
  → (d₂ : Decidable R₂)
  → {F : Function A₁ A₂}
  → (i : FunctionInjective R₁ R₂ F)
  → SplitFunctorSquare
    (functor-list-unit F)
    (functor-collection-unit i)
    (split-functor-collection-unit R₁ d₁)
    (split-functor-collection-unit R₂ d₂)
split-functor-square-collection-unit d₁ d₂ i
  = record
  { partial-functor
    = partial-functor-square-collection-unit d₁ d₂ i
  ; functor
    = functor-square-collection-unit' i
  }

