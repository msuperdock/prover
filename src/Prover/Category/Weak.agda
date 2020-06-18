module Prover.Category.Weak where

open import Prover.Category
  using (Category; Functor; FunctorSquare; functor-compose';
    functor-square-compose)
open import Prover.Prelude

-- ## WeakFunctor

-- ### Definition

-- The data needed for the `partial-functor-sum₂` function.
record WeakFunctor
  {C D : Category}
  (F : Functor D C)
  : Set
  where

  no-eta-equality

  open Functor F using () renaming
    ( base
      to unbase
    ; map
      to unmap
    ; map-identity
      to unmap-identity
    ; map-compose
      to unmap-compose
    )

  field

    map
      : (x' y' : Category.Object D)
      → Category.Arrow C (unbase x') (unbase y')
      → Category.Arrow D x' y'

    map-compose
      : (x' y' z' : Category.Object D)
      → (f : Category.Arrow C (unbase y') (unbase z'))
      → (g : Category.Arrow C (unbase x') (unbase y'))
      → map x' z' (Category.compose C f g)
        ≡ Category.compose D (map y' z' f) (map x' y' g)

    -- `map` of `unmap` acts like identity within composition.
    map-unmap₁
      : {y' z' : Category.Object D}
      → (x' : Category.Object D)
      → (f' : Category.Arrow D y' z')
      → (g : Category.Arrow C (unbase x') (unbase y'))
      → Category.compose D (map y' z' (unmap f')) (map x' y' g)
        ≡ Category.compose D f' (map x' y' g)

    -- `map` of `unmap` acts like identity within composition.
    map-unmap₂
      : {x' y' : Category.Object D}
      → (z' : Category.Object D)
      → (f : Category.Arrow C (unbase y') (unbase z'))
      → (g' : Category.Arrow D x' y')
      → Category.compose D (map y' z' f) (map x' y' (unmap g'))
        ≡ Category.compose D (map y' z' f) g'

  map-eq
    : {x y : Category.Object C}
    → (x' y' : Category.Object D)
    → unbase x' ≡ x
    → unbase y' ≡ y
    → Category.Arrow C x y
    → Category.Arrow D x' y'
  map-eq x' y' refl refl
    = map x' y'

  map-eq'
    : {x y : Category.Object C}
    → (x' y' : Category.Object D)
    → {f₁ : Category.Arrow C x y}
    → {f₂ : Category.Arrow C (unbase x') (unbase y')}
    → (p : unbase x' ≡ x)
    → (q : unbase y' ≡ y)
    → f₂ ≅ f₁
    → map-eq x' y' p q f₁ ≡ map x' y' f₂
  map-eq' _ _ refl refl refl
    = refl

-- ### Compose

module _
  {C D E : Category}
  {F : Functor E D}
  {G : Functor D C}
  where

  module WeakFunctorCompose
    (F' : WeakFunctor F)
    (G' : WeakFunctor G)
    where

    open Functor (functor-compose' G F) using () renaming
      ( base
        to unbase
      ; map
        to unmap
      ; map-identity
        to unmap-identity
      ; map-compose
        to unmap-compose
      )

    map
      : (x' y' : Category.Object E)
      → Category.Arrow C (unbase x') (unbase y')
      → Category.Arrow E x' y'
    map x' y' f
      = WeakFunctor.map F' x' y'
        (WeakFunctor.map G' (Functor.base F x') (Functor.base F y') f)

    abstract

      map-compose
        : (x' y' z' : Category.Object E)
        → (f : Category.Arrow C (unbase y') (unbase z'))
        → (g : Category.Arrow C (unbase x') (unbase y'))
        → map x' z' (Category.compose C f g)
          ≡ Category.compose E (map y' z' f) (map x' y' g)
      map-compose x' y' z' f g
        with WeakFunctor.map G'
          (Functor.base F x')
          (Functor.base F z')
          (Category.compose C f g)
        | WeakFunctor.map-compose G'
          (Functor.base F x')
          (Functor.base F y')
          (Functor.base F z') f g
      ... | _ | refl
        = WeakFunctor.map-compose F' x' y' z'
          (WeakFunctor.map G' (Functor.base F y') (Functor.base F z') f)
          (WeakFunctor.map G' (Functor.base F x') (Functor.base F y') g)
  
      map-unmap₁
        : {y' z' : Category.Object E}
        → (x' : Category.Object E)
        → (f' : Category.Arrow E y' z')
        → (g : Category.Arrow C (unbase x') (unbase y'))
        → Category.compose E (map y' z' (unmap f')) (map x' y' g)
          ≡ Category.compose E f' (map x' y' g)
      map-unmap₁ {y' = y'} {z' = z'} x' f' g
        with Category.compose E (map y' z' (unmap f')) (map x' y' g)
        | sym (WeakFunctor.map-compose F' x' y' z'
          (WeakFunctor.map G' (Functor.base F y') (Functor.base F z') (unmap f'))
          (WeakFunctor.map G' (Functor.base F x') (Functor.base F y') g))
      ... | _ | refl
        with Category.compose D
          (WeakFunctor.map G' (Functor.base F y') (Functor.base F z') (unmap f'))
          (WeakFunctor.map G' (Functor.base F x') (Functor.base F y') g)
        | WeakFunctor.map-unmap₁ G' (Functor.base F x') (Functor.map F f') g
      ... | _ | refl
        with WeakFunctor.map F' x' z' (Category.compose D
          (Functor.map F f')
          (WeakFunctor.map G' (Functor.base F x') (Functor.base F y') g))
        | WeakFunctor.map-compose F' x' y' z'
          (Functor.map F f')
          (WeakFunctor.map G' (Functor.base F x') (Functor.base F y') g)
      ... | _ | refl
        = WeakFunctor.map-unmap₁ F' x' f'
          (WeakFunctor.map G' (Functor.base F x') (Functor.base F y') g)
        
      map-unmap₂
        : {x' y' : Category.Object E}
        → (z' : Category.Object E)
        → (f : Category.Arrow C (unbase y') (unbase z'))
        → (g' : Category.Arrow E x' y')
        → Category.compose E (map y' z' f) (map x' y' (unmap g'))
          ≡ Category.compose E (map y' z' f) g'
      map-unmap₂ {x' = x'} {y' = y'} z' f g'
        with Category.compose E (map y' z' f) (map x' y' (unmap g'))
        | sym (WeakFunctor.map-compose F' x' y' z'
          (WeakFunctor.map G' (Functor.base F y') (Functor.base F z') f)
          (WeakFunctor.map G' (Functor.base F x') (Functor.base F y') (unmap g')))
      ... | _ | refl
        with Category.compose D
          (WeakFunctor.map G' (Functor.base F y') (Functor.base F z') f)
          (WeakFunctor.map G' (Functor.base F x') (Functor.base F y') (unmap g'))
        | WeakFunctor.map-unmap₂ G' (Functor.base F z') f (Functor.map F g')
      ... | _ | refl
        with WeakFunctor.map F' x' z' (Category.compose D
          (WeakFunctor.map G' (Functor.base F y') (Functor.base F z') f)
          (Functor.map F g'))
        | WeakFunctor.map-compose F' x' y' z'
          (WeakFunctor.map G' (Functor.base F y') (Functor.base F z') f)
          (Functor.map F g')
      ... | _ | refl
        = WeakFunctor.map-unmap₂ F' z'
          (WeakFunctor.map G' (Functor.base F y') (Functor.base F z') f) g'

  weak-functor-compose
    : (F' : WeakFunctor F)
    → (G' : WeakFunctor G)
    → WeakFunctor (functor-compose' G F)
  weak-functor-compose F' G'
    = record {WeakFunctorCompose F' G'}

-- ## WeakFunctorSquare

-- ### Definition

record WeakFunctorSquare
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : Functor D₁ C₁}
  {H₂ : Functor D₂ C₂}
  (H₁' : WeakFunctor H₁)
  (H₂' : WeakFunctor H₂)
  (s : FunctorSquare G F H₁ H₂)
  : Set
  where

  field

    map
      : (x₁' y₁' : Category.Object D₁)
      → (f₁ : Category.Arrow C₁
        (Functor.base H₁ x₁')
        (Functor.base H₁ y₁'))
      → WeakFunctor.map-eq H₂'
        (Functor.base G x₁')
        (Functor.base G y₁')
        (FunctorSquare.base s x₁')
        (FunctorSquare.base s y₁')
        (Functor.map F f₁)
      ≡ Functor.map G
        (WeakFunctor.map H₁' x₁' y₁' f₁)

-- ### Compose

module _
  {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H : Functor E₁ E₂}
  {I₁ : Functor E₁ D₁}
  {I₂ : Functor E₂ D₂}
  {J₁ : Functor D₁ C₁}
  {J₂ : Functor D₂ C₂}
  {I₁' : WeakFunctor I₁}
  {I₂' : WeakFunctor I₂}
  {J₁' : WeakFunctor J₁}
  {J₂' : WeakFunctor J₂}
  {s : FunctorSquare H G I₁ I₂}
  {t : FunctorSquare G F J₁ J₂}
  where

  module WeakFunctorSquareCompose
    (s' : WeakFunctorSquare I₁' I₂' s)
    (t' : WeakFunctorSquare J₁' J₂' t)
    where

    map₂
      : {x₂ y₂ : Category.Object C₂}
      → {x₂' y₂' : Category.Object D₂}
      → (x₂'' y₂'' : Category.Object E₂)
      → (p₂ : Functor.base J₂ x₂' ≡ x₂)
      → (p₂' : Functor.base I₂ x₂'' ≡ x₂')
      → (p₂'' : Functor.base (functor-compose' J₂ I₂) x₂'' ≡ x₂)
      → (q₂ : Functor.base J₂ y₂' ≡ y₂)
      → (q₂' : Functor.base I₂ y₂'' ≡ y₂')
      → (q₂'' : Functor.base (functor-compose' J₂ I₂) y₂'' ≡ y₂)
      → (f₂ : Category.Arrow C₂ x₂ y₂)
      → WeakFunctor.map-eq (weak-functor-compose I₂' J₂') x₂'' y₂'' p₂'' q₂'' f₂
      ≡ WeakFunctor.map-eq I₂' x₂'' y₂'' p₂' q₂'
        (WeakFunctor.map-eq J₂' x₂' y₂' p₂ q₂ f₂)
    map₂ _ _ refl refl refl refl refl refl _
      = refl

    map
      : (x₁' y₁' : Category.Object E₁)
      → (f₁ : Category.Arrow C₁
        (Functor.base (functor-compose' J₁ I₁) x₁')
        (Functor.base (functor-compose' J₁ I₁) y₁'))
      → WeakFunctor.map-eq (weak-functor-compose I₂' J₂')
        (Functor.base H x₁')
        (Functor.base H y₁')
        (FunctorSquare.base (functor-square-compose t s) x₁')
        (FunctorSquare.base (functor-square-compose t s) y₁')
        (Functor.map F f₁)
      ≡ Functor.map H
        (WeakFunctor.map (weak-functor-compose I₁' J₁') x₁' y₁' f₁)
    map x₁' y₁' f₁
      = trans
        (map₂
          (Functor.base H x₁')
          (Functor.base H y₁')
          (FunctorSquare.base t (Functor.base I₁ x₁'))
          (FunctorSquare.base s x₁')
          (FunctorSquare.base (functor-square-compose t s) x₁')
          (FunctorSquare.base t (Functor.base I₁ y₁'))
          (FunctorSquare.base s y₁')
          (FunctorSquare.base (functor-square-compose t s) y₁')
          (Functor.map F f₁))
      $ trans
        (sub
          (WeakFunctor.map-eq I₂'
            (Functor.base H x₁')
            (Functor.base H y₁')
            (FunctorSquare.base s x₁')
            (FunctorSquare.base s y₁'))
          (WeakFunctorSquare.map t'
            (Functor.base I₁ x₁')
            (Functor.base I₁ y₁') f₁))
        (WeakFunctorSquare.map s' x₁' y₁'
          (WeakFunctor.map J₁'
            (Functor.base I₁ x₁')
            (Functor.base I₁ y₁') f₁))

  weak-functor-square-compose
    : WeakFunctorSquare I₁' I₂' s
    → WeakFunctorSquare J₁' J₂' t
    → WeakFunctorSquare
      (weak-functor-compose I₁' J₁')
      (weak-functor-compose I₂' J₂')
      (functor-square-compose t s)
  weak-functor-square-compose s' t'
    = record {WeakFunctorSquareCompose s' t'}

