module Prover.Category.Split.Setoid where

open import Prover.Category
  using (Category; Functor; FunctorSquare)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Partial.Setoid
  using (PartialSetoidFunctor; PartialSetoidFunctorSquare;
    partial-functor-setoid; partial-functor-square-setoid)
open import Prover.Category.Setoid
  using (module CategorySetoid; SetoidCategory; SetoidFunctor;
    SetoidFunctorSquare; category-setoid; functor-setoid; functor-square-setoid)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
open import Prover.Prelude

-- ## SplitSetoidFunctor

-- ### Definition

record SplitSetoidFunctor
  (C D : SetoidCategory)
  : Set
  where

  no-eta-equality

  field

    partial-setoid-functor
      : PartialSetoidFunctor C D

  open PartialSetoidFunctor partial-setoid-functor public

  field

    setoid-functor
      : SetoidFunctor D C

  open SetoidFunctor setoid-functor public using () renaming
    ( base
      to unbase
    ; map
      to unmap
    )

  field

    base-unbase
      : (x' : SetoidCategory.Object D)
      → base (unbase x') ≡ just x'

    map-unmap
      : {x' y' : SetoidCategory.Object D}
      → (f' : SetoidCategory.Arrow D x' y')
      → SetoidCategory.ArrowEqual D
        (map (base-unbase x') (base-unbase y') (unmap f')) f'

    normalize-arrow
      : {x' : SetoidCategory.Object D}
      → (x : SetoidCategory.Object C)
      → base x ≡ just x'
      → SetoidCategory.Arrow C x (unbase x')

    normalize-valid
      : {x' : SetoidCategory.Object D}
      → (x : SetoidCategory.Object C)
      → (p : base x ≡ just x')
      → SetoidCategory.ArrowEqual D
        (map p (base-unbase x') (normalize-arrow x p))
        (SetoidCategory.identity D x')

-- ### Conversion

module _
  {C D : SetoidCategory}
  where

  module SplitFunctorSetoid
    (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    (D' : SetoidCategory.Object D → SetoidCategory.Object D → Set)
    (F : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    (G : (x y : SetoidCategory.Object D)
      → SetoidIsomorphism (D' x y) (SetoidCategory.ArrowSetoid D x y))
    (H : SplitSetoidFunctor C D)
    where

    open CategorySetoid
      using (from; from-eq; from-to; to; to-from)
    open SplitSetoidFunctor H public
      using (base-unbase)

    partial-functor
      : PartialFunctor
        (category-setoid C C' F)
        (category-setoid D D' G)
    partial-functor
      = partial-functor-setoid C' D' F G
        (SplitSetoidFunctor.partial-setoid-functor H)

    open PartialFunctor partial-functor

    functor
      : Functor
        (category-setoid D D' G)
        (category-setoid C C' F)
    functor
      = functor-setoid D' C' G F
        (SplitSetoidFunctor.setoid-functor H)

    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    map-unmap
      : {x' y' : Category.Object (category-setoid D D' G)}
      → (f' : Category.Arrow (category-setoid D D' G) x' y')
      → map (base-unbase x') (base-unbase y') (unmap f') ≡ f'
    map-unmap {x' = x'} {y' = y'} f'
      = trans (from-eq D D' G
        (SplitSetoidFunctor.map-eq H (base-unbase x') (base-unbase y')
          (to-from C C' F (SplitSetoidFunctor.unmap H (to D D' G f')))))
      $ trans (from-eq D D' G
        (SplitSetoidFunctor.map-unmap H (to D D' G f')))
      $ from-to D D' G f'

    normalize-arrow
      : {x' : Category.Object (category-setoid D D' G)}
      → (x : Category.Object (category-setoid C C' F))
      → base x ≡ just x'
      → Category.Arrow (category-setoid C C' F) x (unbase x')
    normalize-arrow x p
      = from C C' F
        (SplitSetoidFunctor.normalize-arrow H x p)

    normalize-valid
      : {x' : Category.Object (category-setoid D D' G)}
      → (x : Category.Object (category-setoid C C' F))
      → (p : base x ≡ just x')
      → map p (base-unbase x') (normalize-arrow x p)
        ≡ Category.identity (category-setoid D D' G) x'
    normalize-valid {x' = x'} x p
      = trans (from-eq D D' G
        (SplitSetoidFunctor.map-eq H p (base-unbase x')
          (to-from C C' F (SplitSetoidFunctor.normalize-arrow H x p))))
      $ from-eq D D' G (SplitSetoidFunctor.normalize-valid H x p)

  split-functor-setoid
    : (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    → (D' : SetoidCategory.Object D → SetoidCategory.Object D → Set)
    → (F : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    → (G : (x y : SetoidCategory.Object D)
      → SetoidIsomorphism (D' x y) (SetoidCategory.ArrowSetoid D x y))
    → SplitSetoidFunctor C D
    → SplitFunctor
      (category-setoid C C' F)
      (category-setoid D D' G)
  split-functor-setoid C' D' F G H
    = record {SplitFunctorSetoid C' D' F G H}

-- ## SplitSetoidFunctorSquare

-- ### Definition

record SplitSetoidFunctorSquare
  {C₁ C₂ D₁ D₂ : SetoidCategory}
  (F : SetoidFunctor C₁ C₂)
  (G : SetoidFunctor D₁ D₂)
  (H₁ : SplitSetoidFunctor C₁ D₁)
  (H₂ : SplitSetoidFunctor C₂ D₂)
  : Set
  where

  field

    partial-setoid-functor
      : PartialSetoidFunctorSquare F G
        (SplitSetoidFunctor.partial-setoid-functor H₁)
        (SplitSetoidFunctor.partial-setoid-functor H₂)

  field

    setoid-functor
      : SetoidFunctorSquare G F
        (SplitSetoidFunctor.setoid-functor H₁)
        (SplitSetoidFunctor.setoid-functor H₂)

-- ### Conversion

module _
  {C₁ C₂ D₁ D₂ : SetoidCategory}
  {F : SetoidFunctor C₁ C₂}
  {G : SetoidFunctor D₁ D₂}
  {H₁ : SplitSetoidFunctor C₁ D₁}
  {H₂ : SplitSetoidFunctor C₂ D₂}
  where

  module SplitFunctorSquareSetoid
    (C₁' : SetoidCategory.Object C₁ → SetoidCategory.Object C₁ → Set)
    (C₂' : SetoidCategory.Object C₂ → SetoidCategory.Object C₂ → Set)
    (D₁' : SetoidCategory.Object D₁ → SetoidCategory.Object D₁ → Set)
    (D₂' : SetoidCategory.Object D₂ → SetoidCategory.Object D₂ → Set)
    (I₁ : (x y : SetoidCategory.Object C₁)
      → SetoidIsomorphism (C₁' x y) (SetoidCategory.ArrowSetoid C₁ x y))
    (I₂ : (x y : SetoidCategory.Object C₂)
      → SetoidIsomorphism (C₂' x y) (SetoidCategory.ArrowSetoid C₂ x y))
    (J₁ : (x y : SetoidCategory.Object D₁)
      → SetoidIsomorphism (D₁' x y) (SetoidCategory.ArrowSetoid D₁ x y))
    (J₂ : (x y : SetoidCategory.Object D₂)
      → SetoidIsomorphism (D₂' x y) (SetoidCategory.ArrowSetoid D₂ x y))
    (s : SplitSetoidFunctorSquare F G H₁ H₂)
    where

    partial-functor
      : PartialFunctorSquare
        (functor-setoid C₁' C₂' I₁ I₂ F)
        (functor-setoid D₁' D₂' J₁ J₂ G)
        (SplitFunctor.partial-functor (split-functor-setoid C₁' D₁' I₁ J₁ H₁))
        (SplitFunctor.partial-functor (split-functor-setoid C₂' D₂' I₂ J₂ H₂))
    partial-functor
      = partial-functor-square-setoid C₁' C₂' D₁' D₂' I₁ I₂ J₁ J₂
        (SplitSetoidFunctorSquare.partial-setoid-functor s)

    functor
      : FunctorSquare
        (functor-setoid D₁' D₂' J₁ J₂ G)
        (functor-setoid C₁' C₂' I₁ I₂ F)
        (SplitFunctor.functor (split-functor-setoid C₁' D₁' I₁ J₁ H₁))
        (SplitFunctor.functor (split-functor-setoid C₂' D₂' I₂ J₂ H₂))
    functor
      = functor-square-setoid D₁' D₂' C₁' C₂' J₁ J₂ I₁ I₂
        (SplitSetoidFunctorSquare.setoid-functor s)

  split-functor-square-setoid
    : (C₁' : SetoidCategory.Object C₁ → SetoidCategory.Object C₁ → Set)
    → (C₂' : SetoidCategory.Object C₂ → SetoidCategory.Object C₂ → Set)
    → (D₁' : SetoidCategory.Object D₁ → SetoidCategory.Object D₁ → Set)
    → (D₂' : SetoidCategory.Object D₂ → SetoidCategory.Object D₂ → Set)
    → (I₁ : (x y : SetoidCategory.Object C₁)
      → SetoidIsomorphism (C₁' x y) (SetoidCategory.ArrowSetoid C₁ x y))
    → (I₂ : (x y : SetoidCategory.Object C₂)
      → SetoidIsomorphism (C₂' x y) (SetoidCategory.ArrowSetoid C₂ x y))
    → (J₁ : (x y : SetoidCategory.Object D₁)
      → SetoidIsomorphism (D₁' x y) (SetoidCategory.ArrowSetoid D₁ x y))
    → (J₂ : (x y : SetoidCategory.Object D₂)
      → SetoidIsomorphism (D₂' x y) (SetoidCategory.ArrowSetoid D₂ x y))
    → SplitSetoidFunctorSquare F G H₁ H₂
    → SplitFunctorSquare
      (functor-setoid C₁' C₂' I₁ I₂ F)
      (functor-setoid D₁' D₂' J₁ J₂ G)
      (split-functor-setoid C₁' D₁' I₁ J₁ H₁)
      (split-functor-setoid C₂' D₂' I₂ J₂ H₂)
  split-functor-square-setoid C₁' C₂' D₁' D₂' I₁ I₂ J₁ J₂ s
    = record {SplitFunctorSquareSetoid C₁' C₂' D₁' D₂' I₁ I₂ J₁ J₂ s}

