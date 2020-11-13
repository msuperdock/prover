module Prover.Category.Split.List where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.List
  using (module CategoryList; category-list; functor-list; functor-square-list)
open import Prover.Category.Partial
  using (PartialFunctor)
open import Prover.Category.Partial.List
  using (module PartialFunctorList; partial-functor-list;
    partial-functor-square-list)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Prelude

open List
  using (_!_)

-- ## SplitFunctor

module _
  {C D : Category}
  where

  module SplitFunctorList
    (F : SplitFunctor C D)
    where

    partial-functor
      : PartialFunctor
        (category-list C)
        (category-list D)
    partial-functor
      = partial-functor-list
        (SplitFunctor.partial-functor F)

    open PartialFunctor partial-functor public

    functor
      : Functor
        (category-list D)
        (category-list C)
    functor
      = functor-list
        (SplitFunctor.functor F)

    open Functor functor public using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase'
        : {n : ℕ}
        → (xs : Vec (Category.Object D) n)
        → Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) xs)
        ≡ just xs
      base-unbase' nil
        = refl
      base-unbase' (cons x (any xs))
        with SplitFunctor.base F (SplitFunctor.unbase F x)
        | SplitFunctor.base-unbase F x
        | Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) xs)
        | base-unbase' xs
      ... | _ | refl | _ | refl
        = refl

      base-unbase
        : (xs : Category.Object (category-list D))
        → base (unbase xs) ≡ just xs
      base-unbase (any xs)
        = sub (Maybe.map any) (base-unbase' xs)

      map-unmap'
        : {xs ys : Category.Object (category-list D)}
        → (fs : Category.Arrow (category-list D) xs ys)
        → (k : Fin (List.length xs))
        → CategoryList.LookupEqual D xs ys k
          (PartialFunctorList.map-lookup
            (SplitFunctor.partial-functor F)
            (base-unbase xs)
            (base-unbase ys)
            (unmap fs) k)
          (CategoryList.Arrow.lookup fs k)
      map-unmap' {xs = any xs} {ys = any ys} fs k
        with Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) xs)
        | inspect (Vec.map-maybe (SplitFunctor.base F))
          (Vec.map (SplitFunctor.unbase F) xs)
        | base-unbase' xs
        | Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) ys)
        | inspect (Vec.map-maybe (SplitFunctor.base F))
          (Vec.map (SplitFunctor.unbase F) ys)
        | base-unbase' ys
      ... | _ | [ p ] | refl | _ | [ q ] | refl
        with CategoryList.Arrow.lookup fs k
      ... | nothing
        = CategoryList.nothing
      ... | just (l , f)
        = CategoryList.just l
        $ Category.any' D
        $ Category.arrow-trans' D (SplitFunctor.map-equal' F p'' p''' q'' q'''
          (Category.arrow-equal' C p' q' (SplitFunctor.unmap F f)))
        $ SplitFunctor.map-unmap'' F p''' q''' f
        where
          p' = Vec.lookup-map (SplitFunctor.unbase F) xs k
          q' = Vec.lookup-map (SplitFunctor.unbase F) ys l
          p'' = Vec.lookup-map-maybe (SplitFunctor.base F)
            (Vec.map (SplitFunctor.unbase F) xs) p k
          q'' = Vec.lookup-map-maybe (SplitFunctor.base F)
            (Vec.map (SplitFunctor.unbase F) ys) q l
          p''' = SplitFunctor.base-unbase F (Vec.lookup xs k)
          q''' = SplitFunctor.base-unbase F (Vec.lookup ys l)

      map-unmap
        : {xs ys : Category.Object (category-list D)}
        → (fs : Category.Arrow (category-list D) xs ys)
        → Category.ArrowEqual (category-list D)
          (map (base-unbase xs) (base-unbase ys) (unmap fs)) fs
      map-unmap fs
        = record
        { lookup
          = map-unmap' fs
        }

      normalize-lookup'
        : {n : ℕ}
        → {xs' : Vec (Category.Object D) n}
        → (xs : Vec (Category.Object C) n)
        → Vec.map-maybe (SplitFunctor.base F) xs ≡ just xs'
        → (k : Fin n)
        → Category.Arrow C
          (Vec.lookup xs k)
          (Vec.lookup (Vec.map (SplitFunctor.unbase F) xs') k)
      normalize-lookup' {xs' = xs'} xs p k
        with Vec.lookup (Vec.map (SplitFunctor.unbase F) xs') k
        | Vec.lookup-map (SplitFunctor.unbase F) xs' k
      ... | _ | refl
        = SplitFunctor.normalize-arrow F (Vec.lookup xs k)
          (Vec.lookup-map-maybe (SplitFunctor.base F) xs p k)

      normalize-lookup-equal
        : {n : ℕ}
        → {xs' : Vec (Category.Object D) n}
        → (xs : Vec (Category.Object C) n)
        → (p : Vec.map-maybe (SplitFunctor.base F) xs ≡ just xs')
        → (k : Fin n)
        → Category.ArrowEqual' C
          (normalize-lookup' xs p k)
          (SplitFunctor.normalize-arrow F
            (Vec.lookup xs k)
            (Vec.lookup-map-maybe (SplitFunctor.base F) xs p k))
      normalize-lookup-equal {xs' = xs'} _ _ k
        with Vec.lookup (Vec.map (SplitFunctor.unbase F) xs') k
        | Vec.lookup-map (SplitFunctor.unbase F) xs' k
      ... | _ | refl
        = Category.arrow-refl' C

      normalize-lookup
        : {xs' : Category.Object (category-list D)}
        → (xs : Category.Object (category-list C))
        → base xs ≡ just xs'
        → (k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length (unbase xs'))
          × Category.Arrow C (xs ! k) (unbase xs' ! l))
      normalize-lookup (any xs) _ _
        with Vec.map-maybe (SplitFunctor.base F) xs
        | inspect (Vec.map-maybe (SplitFunctor.base F)) xs
      normalize-lookup (any xs) refl k | just _ | [ p ]
        = just (k , normalize-lookup' xs p k)

      normalize-injective
        : {xs' : Category.Object (category-list D)}
        → (xs : Category.Object (category-list C))
        → (p : base xs ≡ just xs')
        → (k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length (unbase xs'))}
        → {f₁ : Category.Arrow C (xs ! k₁) (unbase xs' ! l)}
        → {f₂ : Category.Arrow C (xs ! k₂) (unbase xs' ! l)}
        → normalize-lookup xs p k₁ ≡ just (l , f₁)
        → normalize-lookup xs p k₂ ≡ just (l , f₂)
        → k₁ ≡ k₂
      normalize-injective (any xs) _ _ _ _ _
        with Vec.map-maybe (SplitFunctor.base F) xs
        | inspect (Vec.map-maybe (SplitFunctor.base F)) xs
      normalize-injective _ refl _ _ refl refl | just _ | _
        = refl

      normalize-arrow
        : {xs' : Category.Object (category-list D)}
        → (xs : Category.Object (category-list C))
        → base xs ≡ just xs'
        → Category.Arrow (category-list C) xs (unbase xs')
      normalize-arrow xs p
        = record
        { lookup
          = normalize-lookup xs p
        ; injective
          = normalize-injective xs p
        }

      normalize-valid'
        : {xs' : Category.Object (category-list D)}
        → (xs : Category.Object (category-list C))
        → (p : base xs ≡ just xs')
        → (k : Fin (List.length xs'))
        → CategoryList.LookupEqual D xs' xs' k
          (PartialFunctorList.map-lookup
            (SplitFunctor.partial-functor F) p
            (base-unbase xs')
            (normalize-arrow xs p) k)
          (CategoryList.identity-lookup D xs' k)
      normalize-valid' {xs' = any xs'} (any xs) p k
        with normalize-arrow (any xs) p
        | inspect CategoryList.Arrow.lookup (normalize-arrow (any xs) p)
      ... | _ | _
        with Vec.map-maybe (SplitFunctor.base F) xs
        | inspect (Vec.map-maybe (SplitFunctor.base F)) xs
        | Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) xs')
        | inspect (Vec.map-maybe (SplitFunctor.base F))
          (Vec.map (SplitFunctor.unbase F) xs')
        | base-unbase' xs'
      normalize-valid' {xs' = any xs'} (any xs) refl k
        | _ | [ refl ] | just _ | [ p ] | just _ | [ p' ] | refl
        = CategoryList.just k
        $ Category.any' D
        $ Category.arrow-trans' D (SplitFunctor.map-equal' F q q q' r
          (normalize-lookup-equal xs p k))
        $ SplitFunctor.normalize-valid' F (Vec.lookup xs k) q q r
        where
          q = Vec.lookup-map-maybe (SplitFunctor.base F) xs p k
          q' = Vec.lookup-map-maybe (SplitFunctor.base F)
            (Vec.map (SplitFunctor.unbase F) xs') p' k
          r = SplitFunctor.base-unbase F (Vec.lookup xs' k)

      normalize-valid
        : {xs' : Category.Object (category-list D)}
        → (xs : Category.Object (category-list C))
        → (p : base xs ≡ just xs')
        → Category.ArrowEqual (category-list D)
          (map p (base-unbase xs') (normalize-arrow xs p))
          (Category.identity (category-list D) xs')
      normalize-valid xs p
        = record
        { lookup
          = normalize-valid' xs p
        }

  split-functor-list
    : SplitFunctor C D
    → SplitFunctor
      (category-list C)
      (category-list D)
  split-functor-list F
    = record {SplitFunctorList F}

-- ## SplitFunctorSquare

split-functor-square-list
  : {C₁ C₂ D₁ D₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : SplitFunctor C₁ D₁}
  → {H₂ : SplitFunctor C₂ D₂}
  → SplitFunctorSquare F G H₁ H₂
  → SplitFunctorSquare
    (functor-list F)
    (functor-list G)
    (split-functor-list H₁)
    (split-functor-list H₂)
split-functor-square-list s
  = record
  { partial-functor
    = partial-functor-square-list
      (SplitFunctorSquare.partial-functor s)
  ; functor
    = functor-square-list
      (SplitFunctorSquare.functor s)
  }

