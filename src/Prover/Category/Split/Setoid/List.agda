module Prover.Category.Split.Setoid.List where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Partial.Setoid
  using (PartialSetoidFunctor; PartialSetoidFunctorSquare)
open import Prover.Category.Partial.Setoid.List
  using (module PartialSetoidFunctorList; partial-setoid-functor-list;
    partial-setoid-functor-square-list)
open import Prover.Category.Setoid
  using (SetoidCategory; SetoidFunctor; SetoidFunctorSquare)
open import Prover.Category.Setoid.List
  using (module SetoidCategoryList; setoid-category-list; setoid-functor-list;
    setoid-functor-square-list)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Category.Split.Setoid
  using (SplitSetoidFunctor; SplitSetoidFunctorSquare)
open import Prover.Prelude

open List
  using (_!_)

-- ## SplitSetoidFunctor

module _
  {C D : Category}
  where

  module SplitSetoidFunctorList
    (F : SplitFunctor C D)
    where

    partial-setoid-functor
      : PartialSetoidFunctor
        (setoid-category-list C)
        (setoid-category-list D)
    partial-setoid-functor
      = partial-setoid-functor-list
        (SplitFunctor.partial-functor F)

    open PartialSetoidFunctor partial-setoid-functor

    setoid-functor
      : SetoidFunctor
        (setoid-category-list D)
        (setoid-category-list C)
    setoid-functor
      = setoid-functor-list
        (SplitFunctor.functor F)

    open SetoidFunctor setoid-functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase'
        : {n : ℕ}
        → (xs' : Vec (Category.Object D) n)
        → Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) xs')
        ≡ just xs'
      base-unbase' nil
        = refl
      base-unbase' (cons x' (any xs'))
        with SplitFunctor.base F (SplitFunctor.unbase F x')
        | SplitFunctor.base-unbase F x'
        | Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) xs')
        | base-unbase' xs'
      ... | _ | refl | _ | refl
        = refl

      base-unbase
        : (xs' : SetoidCategory.Object (setoid-category-list D))
        → base (unbase xs') ≡ just xs'
      base-unbase (any xs')
        with Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) xs')
        | base-unbase' xs'
      ... | _ | refl
        = refl

      map-unmap'
        : {xs' ys' : SetoidCategory.Object (setoid-category-list D)}
        → (fs' : SetoidCategory.Arrow (setoid-category-list D) xs' ys')
        → (k : Fin (List.length xs'))
        → PartialSetoidFunctorList.map-lookup
          (SplitFunctor.partial-functor F)
          (base-unbase xs')
          (base-unbase ys')
          (unmap fs') k
        ≡ SetoidCategoryList.Arrow.lookup fs' k
      map-unmap' {xs' = any xs'} {ys' = any ys'} fs' k
        with Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) xs')
        | inspect (Vec.map-maybe (SplitFunctor.base F))
          (Vec.map (SplitFunctor.unbase F) xs')
        | base-unbase' xs'
        | Vec.map-maybe (SplitFunctor.base F)
          (Vec.map (SplitFunctor.unbase F) ys')
        | inspect (Vec.map-maybe (SplitFunctor.base F))
          (Vec.map (SplitFunctor.unbase F) ys')
        | base-unbase' ys'
      ... | _ | [ p ] | refl | _ | [ q ] | refl
        with SetoidCategoryList.Arrow.lookup fs' k
      ... | nothing
        = refl
      ... | just (l , f)
        = sub just
        $ Sigma.comma-eq refl
        $ trans (SplitFunctor.map-eq F
          (Vec.lookup-map-maybe (SplitFunctor.base F)
            (Vec.map (SplitFunctor.unbase F) xs') p k)
          (SplitFunctor.base-unbase F (Vec.lookup xs' k))
          (Vec.lookup-map-maybe (SplitFunctor.base F)
            (Vec.map (SplitFunctor.unbase F) ys') q l)
          (SplitFunctor.base-unbase F (Vec.lookup ys' l)) p' q'
          (Category.arrow-eq C p' q' (SplitFunctor.unmap F f)))
        $ SplitFunctor.map-unmap F f
        where
          p' = Vec.lookup-map (SplitFunctor.unbase F) xs' k
          q' = Vec.lookup-map (SplitFunctor.unbase F) ys' l

      map-unmap
        : {xs' ys' : SetoidCategory.Object (setoid-category-list D)}
        → (fs' : SetoidCategory.Arrow (setoid-category-list D) xs' ys')
        → SetoidCategory.ArrowEqual (setoid-category-list D)
          (map (base-unbase xs') (base-unbase ys') (unmap fs')) fs'
      map-unmap fs'
        = SetoidCategoryList.arrow-equal (map-unmap' fs')

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

      normalize-lookup-eq
        : {n : ℕ}
        → {xs' : Vec (Category.Object D) n}
        → (xs : Vec (Category.Object C) n)
        → (p : Vec.map-maybe (SplitFunctor.base F) xs ≡ just xs')
        → (k : Fin n)
        → normalize-lookup' xs p k
        ≅ SplitFunctor.normalize-arrow F
          (Vec.lookup xs k)
          (Vec.lookup-map-maybe (SplitFunctor.base F) xs p k)
      normalize-lookup-eq {xs' = xs'} _ _ k
        with Vec.lookup (Vec.map (SplitFunctor.unbase F) xs') k
        | Vec.lookup-map (SplitFunctor.unbase F) xs' k
      ... | _ | refl
        = refl

      normalize-lookup
        : {xs' : SetoidCategory.Object (setoid-category-list D)}
        → (xs : SetoidCategory.Object (setoid-category-list C))
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
        : {xs' : SetoidCategory.Object (setoid-category-list D)}
        → (xs : SetoidCategory.Object (setoid-category-list C))
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
      normalize-injective _ refl _ _ refl refl | just _ | [ _ ]
        = refl

      normalize-arrow
        : {xs' : SetoidCategory.Object (setoid-category-list D)}
        → (xs : SetoidCategory.Object (setoid-category-list C))
        → base xs ≡ just xs'
        → SetoidCategory.Arrow (setoid-category-list C) xs (unbase xs')
      normalize-arrow xs p
        = record
        { lookup
          = normalize-lookup xs p
        ; injective
          = normalize-injective xs p
        }

      normalize-valid'
        : {xs' : SetoidCategory.Object (setoid-category-list D)}
        → (xs : SetoidCategory.Object (setoid-category-list C))
        → (p : base xs ≡ just xs')
        → (k : Fin (List.length xs'))
        → PartialSetoidFunctorList.map-lookup
          (SplitFunctor.partial-functor F) p
          (base-unbase xs')
          (normalize-arrow xs p) k
        ≡ SetoidCategoryList.identity-lookup D xs' k
      normalize-valid' {xs' = any xs'} (any xs) p k
        with normalize-arrow (any xs) p
        | inspect SetoidCategoryList.Arrow.lookup (normalize-arrow (any xs) p)
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
        = sub just
        $ Sigma.comma-eq refl
        $ trans (SplitFunctor.map-eq F q q
          (Vec.lookup-map-maybe (SplitFunctor.base F)
            (Vec.map (SplitFunctor.unbase F) xs') p' k)
          (SplitFunctor.base-unbase F (Vec.lookup xs' k)) refl
          (Vec.lookup-map (SplitFunctor.unbase F) xs' k)
          (normalize-lookup-eq xs p k))
        $ SplitFunctor.normalize-valid F (Vec.lookup xs k) q
        where
          q = Vec.lookup-map-maybe (SplitFunctor.base F) xs p k

      normalize-valid
        : {xs' : SetoidCategory.Object (setoid-category-list D)}
        → (xs : SetoidCategory.Object (setoid-category-list C))
        → (p : base xs ≡ just xs')
        → SetoidCategory.ArrowEqual (setoid-category-list D)
          (map p (base-unbase xs') (normalize-arrow xs p))
          (SetoidCategory.identity (setoid-category-list D) xs')
      normalize-valid xs p
        = SetoidCategoryList.arrow-equal (normalize-valid' xs p)

  split-setoid-functor-list
    : SplitFunctor C D
    → SplitSetoidFunctor
      (setoid-category-list C)
      (setoid-category-list D)
  split-setoid-functor-list F
    = record {SplitSetoidFunctorList F}

-- ## SplitSetoidFunctorSquare

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : SplitFunctor C₁ D₁}
  {H₂ : SplitFunctor C₂ D₂}
  where

  module SplitSetoidFunctorSquareList
    (s : SplitFunctorSquare F G H₁ H₂)
    where

    partial-setoid-functor
      : PartialSetoidFunctorSquare
        (setoid-functor-list F)
        (setoid-functor-list G)
        (SplitSetoidFunctor.partial-setoid-functor
          (split-setoid-functor-list H₁))
        (SplitSetoidFunctor.partial-setoid-functor
          (split-setoid-functor-list H₂))
    partial-setoid-functor
      = partial-setoid-functor-square-list
        (SplitFunctorSquare.partial-functor s)

    setoid-functor
      : SetoidFunctorSquare
        (setoid-functor-list G)
        (setoid-functor-list F)
        (SplitSetoidFunctor.setoid-functor
          (split-setoid-functor-list H₁))
        (SplitSetoidFunctor.setoid-functor
          (split-setoid-functor-list H₂))
    setoid-functor
      = setoid-functor-square-list
        (SplitFunctorSquare.functor s)

  split-setoid-functor-square-list
    : SplitFunctorSquare F G H₁ H₂
    → SplitSetoidFunctorSquare
      (setoid-functor-list F)
      (setoid-functor-list G)
      (split-setoid-functor-list H₁)
      (split-setoid-functor-list H₂)
  split-setoid-functor-square-list s
    = record {SplitSetoidFunctorSquareList s}

