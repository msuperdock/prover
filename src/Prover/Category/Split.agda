module Prover.Category.Split where

open import Prover.Category
  using (Category; Functor; FunctorSquare; functor-compose';
    functor-square-compose)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare; partial-functor-compose;
    partial-functor-square-compose)
open import Prover.Category.Weak
  using (WeakFunctor; WeakFunctorSquare)
open import Prover.Function.Split
  using (SplitFunction; SplitFunctionSquare)
open import Prover.Prelude

-- ## SplitFunctor

-- ### Definition

record SplitFunctor
  (C D : Category)
  : Set
  where

  no-eta-equality

  field

    partial-functor
      : PartialFunctor C D

  open PartialFunctor partial-functor public

  field

    functor
      : Functor D C

  open Functor functor public using () renaming
    ( base
      to unbase
    ; function
      to function
    ; map
      to unmap
    )

  field

    base-unbase
      : (x : Category.Object D)
      → base (unbase x) ≡ just x

  split-function
    : SplitFunction
      (Category.Object C)
      (Category.Object D)
  split-function
    = record
    { partial-function
      = partial-function
    ; function
      = function
    ; base-unbase
      = base-unbase
    }

  field

    map-unmap
      : {x y : Category.Object D}
      → (f : Category.Arrow D x y)
      → Category.ArrowEqual D
        (map (base-unbase x) (base-unbase y) (unmap f)) f

    normalize-arrow
      : {x' : Category.Object D}
      → (x : Category.Object C)
      → base x ≡ just x'
      → Category.Arrow C x (unbase x')

    normalize-valid
      : {x' : Category.Object D}
      → (x : Category.Object C)
      → (p : base x ≡ just x')
      → Category.ArrowEqual D
        (map p (base-unbase x') (normalize-arrow x p))
        (Category.identity D x')

  map-unmap'
    : {x y : Category.Object D}
    → (p : base (unbase x) ≡ just x)
    → (q : base (unbase y) ≡ just y)
    → (f : Category.Arrow D x y)
    → Category.ArrowEqual D
      (map p q (unmap f)) f
  map-unmap' {x = x} {y = y} p q
    with irrelevant p (base-unbase x)
    | irrelevant q (base-unbase y)
  ... | refl | refl
    = map-unmap

  map-unmap''
    : {x x' y y' : Category.Object D}
    → (p : base (unbase x) ≡ just x')
    → (q : base (unbase y) ≡ just y')
    → (f : Category.Arrow D x y)
    → Category.ArrowEqual' D
      (map p q (unmap f)) f
  map-unmap'' {x = x} {y = y} p q f
    with trans (sym p) (base-unbase x)
    | trans (sym q) (base-unbase y)
  ... | refl | refl
    = Category.any (map-unmap' p q f)

  normalize-valid'
    : {x' x'' : Category.Object D}
    → (x : Category.Object C)
    → (p : base x ≡ just x')
    → (p' : base x ≡ just x'')
    → (q : base (unbase x') ≡ just x')
    → Category.ArrowEqual' D
      (map p' q (normalize-arrow x p))
      (Category.identity D x')
  normalize-valid' {x' = x'} x p p' q
    with trans (sym p) p'
  ... | refl
    with irrelevant p p'
    | irrelevant q (base-unbase x')
  ... | refl | refl
    = Category.any (normalize-valid x p)

-- ### Compose

module _
  {C D E : Category}
  where

  module SplitFunctorCompose
    (F : SplitFunctor D E)
    (G : SplitFunctor C D)
    where

    partial-functor
      : PartialFunctor C E
    partial-functor
      = partial-functor-compose
        (SplitFunctor.partial-functor F)
        (SplitFunctor.partial-functor G)
  
    open PartialFunctor partial-functor

    functor
      : Functor E C
    functor
      = functor-compose'
        (SplitFunctor.functor G)
        (SplitFunctor.functor F)
  
    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    abstract

      base-unbase
        : (x : Category.Object E)
        → base (unbase x) ≡ just x
      base-unbase x
        with SplitFunctor.base G
          (SplitFunctor.unbase G (SplitFunctor.unbase F x))
        | SplitFunctor.base-unbase G (SplitFunctor.unbase F x)
      ... | _ | refl
        = SplitFunctor.base-unbase F x
  
      map-unmap
        : {x y : Category.Object E}
        → (f : Category.Arrow E x y)
        → Category.ArrowEqual E
          (map (base-unbase x) (base-unbase y) (unmap f)) f
      map-unmap {x = x} {y = y} f
        with SplitFunctor.base G
          (SplitFunctor.unbase G (SplitFunctor.unbase F x))
        | SplitFunctor.base-unbase G (SplitFunctor.unbase F x)
        | inspect (SplitFunctor.base G)
          (SplitFunctor.unbase G (SplitFunctor.unbase F x))
        | SplitFunctor.base G (SplitFunctor.unbase G
          (SplitFunctor.unbase F y))
        | SplitFunctor.base-unbase G (SplitFunctor.unbase F y)
        | inspect (SplitFunctor.base G)
          (SplitFunctor.unbase G (SplitFunctor.unbase F y))
      ... | _ | refl | [ p' ] | _ | refl | [ q' ]
        with irrelevant p'
          (SplitFunctor.base-unbase G (SplitFunctor.unbase F x))
        | irrelevant q'
          (SplitFunctor.base-unbase G (SplitFunctor.unbase F y))
      ... | refl | refl
        = Category.arrow-trans E (SplitFunctor.map-equal F p q
          (SplitFunctor.map-unmap G f'))
        $ SplitFunctor.map-unmap F f
        where
          f' = SplitFunctor.unmap F f
          p = SplitFunctor.base-unbase F x
          q = SplitFunctor.base-unbase F y

      normalize-arrow
        : {x' : Category.Object E}
        → (x : Category.Object C)
        → base x ≡ just x'
        → Category.Arrow C x (unbase x')
      normalize-arrow x p'
        with SplitFunctor.base G x
        | inspect (SplitFunctor.base G) x
      ... | just x' | [ p ]
        = Category.compose C
          (SplitFunctor.unmap G (SplitFunctor.normalize-arrow F x' p'))
          (SplitFunctor.normalize-arrow G x p)

      normalize-valid
        : {x' : Category.Object E}
        → (x : Category.Object C)
        → (p : base x ≡ just x')
        → Category.ArrowEqual E
          (map p (base-unbase x') (normalize-arrow x p))
          (Category.identity E x')
      normalize-valid {x' = x''} x p'
        with SplitFunctor.base G x
        | inspect (SplitFunctor.base G) x
        | SplitFunctor.base G
          (SplitFunctor.unbase G (SplitFunctor.unbase F x''))
        | SplitFunctor.base-unbase G (SplitFunctor.unbase F x'')
        | inspect (SplitFunctor.base G)
          (SplitFunctor.unbase G (SplitFunctor.unbase F x''))
      ... | just x' | [ p ] | _ | refl | [ r ]
        = Category.arrow-trans E (SplitFunctor.map-equal F p' q'
          (SplitFunctor.map-compose G p q r
            (SplitFunctor.unmap G (SplitFunctor.normalize-arrow F x' p'))
            (SplitFunctor.normalize-arrow G x p)))
        $ Category.arrow-trans E (SplitFunctor.map-equal F p' q'
          (Category.compose-equal D
            (SplitFunctor.map-unmap' G q r
              (SplitFunctor.normalize-arrow F x' p'))
            (SplitFunctor.normalize-valid G x p)))
        $ Category.arrow-trans E (SplitFunctor.map-equal F p' q'
          (Category.precompose D (SplitFunctor.normalize-arrow F x' p')))
        $ SplitFunctor.normalize-valid F x' p'
        where
          q = SplitFunctor.base-unbase G x'
          q' = SplitFunctor.base-unbase F x''

  split-functor-compose
    : SplitFunctor D E
    → SplitFunctor C D
    → SplitFunctor C E
  split-functor-compose F G
    = record {SplitFunctorCompose F G}

-- ### Weak

module _
  {C D : Category}
  where
  
  module SplitFunctorWeak
    (F : SplitFunctor C D)
    where

    open Functor (SplitFunctor.functor F) using () renaming
      ( base
        to unbase
      ; map
        to unmap
      )

    map
      : (x y : Category.Object D)
      → Category.Arrow C (unbase x) (unbase y)
      → Category.Arrow D x y
    map x y
      = SplitFunctor.map F
        (SplitFunctor.base-unbase F x)
        (SplitFunctor.base-unbase F y)

    abstract

      map-equal
        : (x y : Category.Object D)
        → {f₁ f₂ : Category.Arrow C (unbase x) (unbase y)}
        → Category.ArrowEqual C f₁ f₂
        → Category.ArrowEqual D (map x y f₁) (map x y f₂)
      map-equal x y
        = SplitFunctor.map-equal F
          (SplitFunctor.base-unbase F x)
          (SplitFunctor.base-unbase F y)

      map-compose
        : (x y z : Category.Object D)
        → (f : Category.Arrow C (unbase y) (unbase z))
        → (g : Category.Arrow C (unbase x) (unbase y))
        → Category.ArrowEqual D
          (map x z (Category.compose C f g))
          (Category.compose D (map y z f) (map x y g))
      map-compose x y z
        = SplitFunctor.map-compose F
          (SplitFunctor.base-unbase F x)
          (SplitFunctor.base-unbase F y)
          (SplitFunctor.base-unbase F z)
  
      map-unmap₁
        : {y z : Category.Object D}
        → (x : Category.Object D)
        → (f : Category.Arrow D y z)
        → (g : Category.Arrow C (unbase x) (unbase y))
        → Category.ArrowEqual D
          (Category.compose D (map y z (unmap f)) (map x y g))
          (Category.compose D f (map x y g))
      map-unmap₁ _ f _
        = Category.compose-equal D
          (SplitFunctor.map-unmap F f)
          (Category.arrow-refl D)
  
      map-unmap₂
        : {x y : Category.Object D}
        → (z : Category.Object D)
        → (f : Category.Arrow C (unbase y) (unbase z))
        → (g : Category.Arrow D x y)
        → Category.ArrowEqual D
          (Category.compose D (map y z f) (map x y (unmap g)))
          (Category.compose D (map y z f) g)
      map-unmap₂ _ _ g
        = Category.compose-equal D
          (Category.arrow-refl D)
          (SplitFunctor.map-unmap F g)

  split-functor-weak
    : (F : SplitFunctor C D)
    → WeakFunctor (SplitFunctor.functor F)
  split-functor-weak F
    = record {SplitFunctorWeak F}

-- ## SplitFunctorSquare

-- ### Definition

record SplitFunctorSquare
  {C₁ C₂ D₁ D₂ : Category}
  (F : Functor C₁ C₂)
  (G : Functor D₁ D₂)
  (H₁ : SplitFunctor C₁ D₁)
  (H₂ : SplitFunctor C₂ D₂)
  : Set
  where

  field

    partial-functor
      : PartialFunctorSquare F G
        (SplitFunctor.partial-functor H₁)
        (SplitFunctor.partial-functor H₂)

  open PartialFunctorSquare partial-functor public

  field

    functor
      : FunctorSquare G F
        (SplitFunctor.functor H₁)
        (SplitFunctor.functor H₂)

  open FunctorSquare functor public using () renaming
    ( base
      to unbase
    ; function
      to function
    )

  split-function
    : SplitFunctionSquare
      (Functor.function F)
      (Functor.function G)
      (SplitFunctor.split-function H₁)
      (SplitFunctor.split-function H₂)
  split-function
    = record
    { partial-function
      = partial-function
    ; function
      = function
    }

-- ### Compose

split-functor-square-compose
  : {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H : Functor E₁ E₂}
  → {I₁ : SplitFunctor D₁ E₁}
  → {I₂ : SplitFunctor D₂ E₂}
  → {J₁ : SplitFunctor C₁ D₁}
  → {J₂ : SplitFunctor C₂ D₂}
  → SplitFunctorSquare G H I₁ I₂
  → SplitFunctorSquare F G J₁ J₂
  → SplitFunctorSquare F H
    (split-functor-compose I₁ J₁)
    (split-functor-compose I₂ J₂)
split-functor-square-compose s t
  = record
  { partial-functor
    = partial-functor-square-compose
      (SplitFunctorSquare.partial-functor s)
      (SplitFunctorSquare.partial-functor t)
  ; functor
    = functor-square-compose
      (SplitFunctorSquare.functor t)
      (SplitFunctorSquare.functor s)
  }

-- ### Weak

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : SplitFunctor C₁ D₁}
  {H₂ : SplitFunctor C₂ D₂}
  where

  module SplitFunctorSquareWeak
    (s : SplitFunctorSquare F G H₁ H₂)
    where

    map₂
      : {x₂ y₂ : Category.Object C₂}
      → (x₂' y₂' : Category.Object D₂)
      → (p₂ : SplitFunctor.base H₂ x₂ ≡ just x₂')
      → (q₂ : SplitFunctor.base H₂ y₂ ≡ just y₂')
      → (p₂' : SplitFunctor.unbase H₂ x₂' ≡ x₂)
      → (q₂' : SplitFunctor.unbase H₂ y₂' ≡ y₂)
      → (f₂ : Category.Arrow C₂ x₂ y₂)
      → Category.ArrowEqual D₂
        (WeakFunctor.map' (split-functor-weak H₂) x₂' y₂' p₂' q₂' f₂)
        (SplitFunctor.map H₂ p₂ q₂ f₂)
    map₂ x₂' y₂' p₂ q₂ refl refl _
      with irrelevant p₂ (SplitFunctor.base-unbase H₂ x₂')
      | irrelevant q₂ (SplitFunctor.base-unbase H₂ y₂')
    ... | refl | refl
      = Category.arrow-refl D₂

    map
      : (x₁ y₁ : Category.Object D₁)
      → (p : Functor.base (SplitFunctor.functor H₂) (Functor.base G x₁)
        ≡ Functor.base F (Functor.base (SplitFunctor.functor H₁) x₁))
      → (q : Functor.base (SplitFunctor.functor H₂) (Functor.base G y₁)
        ≡ Functor.base F (Functor.base (SplitFunctor.functor H₁) y₁))
      → (f₁ : Category.Arrow C₁
        (Functor.base (SplitFunctor.functor H₁) x₁)
        (Functor.base (SplitFunctor.functor H₁) y₁))
      → Category.ArrowEqual D₂
        (WeakFunctor.map'
          (split-functor-weak H₂)
          (Functor.base G x₁)
          (Functor.base G y₁) p q
          (Functor.map F f₁))
        (Functor.map G
          (WeakFunctor.map (split-functor-weak H₁) x₁ y₁ f₁))
    map x₁ y₁ p q f₁
      = Category.arrow-trans D₂ (map₂ x₂ y₂ p'' q'' p q f₂)
      $ SplitFunctorSquare.map s p' q' f₁
      where
        x₂ = Functor.base G x₁
        y₂ = Functor.base G y₁
        f₂ = Functor.map F f₁
        p' = SplitFunctor.base-unbase H₁ x₁
        q' = SplitFunctor.base-unbase H₁ y₁
        p'' = SplitFunctorSquare.base s (SplitFunctor.unbase H₁ x₁) p'
        q'' = SplitFunctorSquare.base s (SplitFunctor.unbase H₁ y₁) q'

  split-functor-square-weak
    : SplitFunctorSquare F G H₁ H₂
    → WeakFunctorSquare F G
      (split-functor-weak H₁)
      (split-functor-weak H₂)
  split-functor-square-weak s
    = record {SplitFunctorSquareWeak s}

