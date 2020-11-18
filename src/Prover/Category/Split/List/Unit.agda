module Prover.Category.Split.List.Unit where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.List
  using (category-list; functor-list)
open import Prover.Category.List.Unit
  using (module CategoryListUnit; module FunctorListUnit'; category-list-unit;
    functor-list-unit; functor-list-unit'; functor-list-unit'';
    functor-square-list-unit'; functor-square-list-unit'')
open import Prover.Category.Unit
  using (category-unit; functor-unit)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare; TotalSplitFunctor;
    TotalSplitFunctorSquare; total-split-functor-partial;
    total-split-functor-square-partial)
open import Prover.Function
  using (Function)
open import Prover.Prelude

-- ## TotalSplitFunctor

module TotalSplitFunctorListUnit
  (A : Set)
  where

  functor
    : Functor
      (category-list (category-unit A))
      (category-list-unit A)
  functor
    = functor-list-unit' A

  open Functor functor

  functor'
    : Functor
      (category-list-unit A)
      (category-list (category-unit A))
  functor'
    = functor-list-unit'' A

  open Functor functor' using () renaming
    ( base
      to unbase
    ; map
      to unmap
    )

  abstract

    unbase-base
      : (xs : Category.Object (category-list (category-unit A)))
      → unbase (base xs) ≡ xs
    unbase-base _
      = refl

    base-unbase
      : (xs : Category.Object (category-list-unit A))
      → base (unbase xs) ≡ xs
    base-unbase _
      = refl

    map-unmap-lookup
      : {xs ys : Category.Object (category-list-unit A)}
      → (fs : Category.Arrow (category-list-unit A) xs ys)
      → (k : Fin (List.length xs))
      → FunctorListUnit'.map-lookup A (Functor.map (functor-list-unit'' A) fs) k
        ≡ CategoryListUnit.Arrow.lookup fs k
    map-unmap-lookup fs k
      with CategoryListUnit.Arrow.lookup fs k
    ... | nothing
      = refl
    ... | just _
      = refl

    map-unmap
      : {xs ys : Category.Object (category-list-unit A)}
      → (fs : Category.Arrow (category-list-unit A) xs ys)
      → Category.ArrowEqual' (category-list-unit A) (map (unmap fs)) fs
    map-unmap fs
      = Category.any
      $ record
      { lookup
        = map-unmap-lookup fs
      }

total-split-functor-list-unit
  : (A : Set)
  → TotalSplitFunctor
    (category-list (category-unit A))
    (category-list-unit A)
total-split-functor-list-unit A
  = record {TotalSplitFunctorListUnit A}

-- ## TotalSplitFunctorSquare

total-split-functor-square-list-unit
  : {A₁ A₂ : Set}
  → (F : Function A₁ A₂)
  → TotalSplitFunctorSquare
    (functor-list (functor-unit F))
    (functor-list-unit F)
    (total-split-functor-list-unit A₁)
    (total-split-functor-list-unit A₂)
total-split-functor-square-list-unit F
  = record
  { functor
    = functor-square-list-unit' F
  ; functor'
    = functor-square-list-unit'' F
  }

-- ## SplitFunctor

split-functor-list-unit
  : (A : Set)
  → SplitFunctor
    (category-list (category-unit A))
    (category-list-unit A)
split-functor-list-unit A
  = total-split-functor-partial
  $ total-split-functor-list-unit A

-- ## SplitFunctorSquare

split-functor-square-list-unit
  : {A₁ A₂ : Set}
  → (F : Function A₁ A₂)
  → SplitFunctorSquare
    (functor-list (functor-unit F))
    (functor-list-unit F)
    (split-functor-list-unit A₁)
    (split-functor-list-unit A₂)
split-functor-square-list-unit F
  = total-split-functor-square-partial
  $ total-split-functor-square-list-unit F

