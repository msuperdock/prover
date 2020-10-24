module Prover.Category.Weak where

open import Prover.Category
  using (Category; Functor; FunctorSquare; any; functor-compose')
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
    )

  field

    map
      : (x y : Category.Object D)
      → Category.Arrow C (unbase x) (unbase y)
      → Category.Arrow D x y

    map-equal
      : (x y : Category.Object D)
      → {f₁ f₂ : Category.Arrow C (unbase x) (unbase y)}
      → Category.ArrowEqual C f₁ f₂
      → Category.ArrowEqual D (map x y f₁) (map x y f₂)

    map-compose
      : (x y z : Category.Object D)
      → (f : Category.Arrow C (unbase y) (unbase z))
      → (g : Category.Arrow C (unbase x) (unbase y))
      → Category.ArrowEqual D
        (map x z (Category.compose C f g))
        (Category.compose D (map y z f) (map x y g))

    -- `map` of `unmap` acts like identity within composition.
    map-unmap₁
      : {y z : Category.Object D}
      → (x : Category.Object D)
      → (f : Category.Arrow D y z)
      → (g : Category.Arrow C (unbase x) (unbase y))
      → Category.ArrowEqual D
        (Category.compose D (map y z (unmap f)) (map x y g))
        (Category.compose D f (map x y g))

    -- `map` of `unmap` acts like identity within composition.
    map-unmap₂
      : {x y : Category.Object D}
      → (z : Category.Object D)
      → (f : Category.Arrow C (unbase y) (unbase z))
      → (g : Category.Arrow D x y)
      → Category.ArrowEqual D
        (Category.compose D (map y z f) (map x y (unmap g)))
        (Category.compose D (map y z f) g)

  map'
    : {x y : Category.Object C}
    → (x' y' : Category.Object D)
    → unbase x' ≡ x
    → unbase y' ≡ y
    → Category.Arrow C x y
    → Category.Arrow D x' y'
  map' x' y' refl refl
    = map x' y'

  map-equal'
    : {x y : Category.Object C}
    → (x' y' : Category.Object D)
    → (p : unbase x' ≡ x)
    → (q : unbase y' ≡ y)
    → {f₁ f₂ : Category.Arrow C x y}
    → Category.ArrowEqual C f₁ f₂
    → Category.ArrowEqual D (map' x' y' p q f₁) (map' x' y' p q f₂)
  map-equal' x' y' refl refl
    = map-equal x' y'

  map-equal''
    : {x₁ x₂ y₁ y₂ : Category.Object C}
    → (x' y' : Category.Object D)
    → (p₁ : unbase x' ≡ x₁)
    → (p₂ : unbase x' ≡ x₂)
    → (q₁ : unbase y' ≡ y₁)
    → (q₂ : unbase y' ≡ y₂)
    → {f₁ : Category.Arrow C x₁ y₁}
    → {f₂ : Category.Arrow C x₂ y₂}
    → Category.ArrowEqual' C f₁ f₂
    → Category.ArrowEqual D (map' x' y' p₁ q₁ f₁) (map' x' y' p₂ q₂ f₂)
  map-equal'' x' y' refl refl refl refl (any p)
    = map-equal x' y' p

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
      )

    map
      : (x y : Category.Object E)
      → Category.Arrow C (unbase x) (unbase y)
      → Category.Arrow E x y
    map x y
      = WeakFunctor.map F' x y
      ∘ WeakFunctor.map G' x' y'
      where
        x' = Functor.base F x
        y' = Functor.base F y

    abstract

      map-equal
        : (x y : Category.Object E)
        → {f₁ f₂ : Category.Arrow C (unbase x) (unbase y)}
        → Category.ArrowEqual C f₁ f₂
        → Category.ArrowEqual E (map x y f₁) (map x y f₂)
      map-equal x y
        = WeakFunctor.map-equal F' x y
        ∘ WeakFunctor.map-equal G' x' y'
        where
          x' = Functor.base F x
          y' = Functor.base F y

      map-compose
        : (x y z : Category.Object E)
        → (f : Category.Arrow C (unbase y) (unbase z))
        → (g : Category.Arrow C (unbase x) (unbase y))
        → Category.ArrowEqual E
          (map x z (Category.compose C f g))
          (Category.compose E (map y z f) (map x y g))
      map-compose x y z f g
        = Category.arrow-trans E (WeakFunctor.map-equal F' x z
          (WeakFunctor.map-compose G' x' y' z' f g))
        $ WeakFunctor.map-compose F' x y z
          (WeakFunctor.map G' y' z' f)
          (WeakFunctor.map G' x' y' g)
        where
          x' = Functor.base F x
          y' = Functor.base F y
          z' = Functor.base F z
  
      map-unmap₁
        : {y z : Category.Object E}
        → (x : Category.Object E)
        → (f : Category.Arrow E y z)
        → (g : Category.Arrow C (unbase x) (unbase y))
        → Category.ArrowEqual E
          (Category.compose E (map y z (unmap f)) (map x y g))
          (Category.compose E f (map x y g))
      map-unmap₁ {y = y} {z = z} x f g
        = Category.arrow-trans E (Category.arrow-sym E
          (WeakFunctor.map-compose F' x y z
            (WeakFunctor.map G' y' z' (unmap f))
            (WeakFunctor.map G' x' y' g)))
        $ Category.arrow-trans E (WeakFunctor.map-equal F' x z
          (WeakFunctor.map-unmap₁ G' x' f' g))
        $ Category.arrow-trans E (WeakFunctor.map-compose F' x y z f'
          (WeakFunctor.map G' x' y' g))
        $ WeakFunctor.map-unmap₁ F' x f
          (WeakFunctor.map G' x' y' g)
        where
          x' = Functor.base F x
          y' = Functor.base F y
          z' = Functor.base F z
          f' = Functor.map F f
        
      map-unmap₂
        : {x y : Category.Object E}
        → (z : Category.Object E)
        → (f : Category.Arrow C (unbase y) (unbase z))
        → (g : Category.Arrow E x y)
        → Category.ArrowEqual E
          (Category.compose E (map y z f) (map x y (unmap g)))
          (Category.compose E (map y z f) g)
      map-unmap₂ {x = x} {y = y} z f g
        = Category.arrow-trans E (Category.arrow-sym E
          (WeakFunctor.map-compose F' x y z
            (WeakFunctor.map G' y' z' f)
            (WeakFunctor.map G' x' y' (unmap g))))
        $ Category.arrow-trans E (WeakFunctor.map-equal F' x z
          (WeakFunctor.map-unmap₂ G' z' f g'))
        $ Category.arrow-trans E (WeakFunctor.map-compose F' x y z
          (WeakFunctor.map G' y' z' f) g')
        $ WeakFunctor.map-unmap₂ F' z
          (WeakFunctor.map G' y' z' f) g
        where
          x' = Functor.base F x
          y' = Functor.base F y
          z' = Functor.base F z
          g' = Functor.map F g

  weak-functor-compose
    : WeakFunctor F
    → WeakFunctor G
    → WeakFunctor (functor-compose' G F)
  weak-functor-compose F' G'
    = record {WeakFunctorCompose F' G'}

-- ## WeakFunctorSquare

-- ### Definition

record WeakFunctorSquare
  {C₁ C₂ D₁ D₂ : Category}
  (F : Functor C₁ C₂)
  (G : Functor D₁ D₂)
  {H₁ : Functor D₁ C₁}
  {H₂ : Functor D₂ C₂}
  (H₁' : WeakFunctor H₁)
  (H₂' : WeakFunctor H₂)
  : Set
  where

  field

    map
      : (x₁ y₁ : Category.Object D₁)
      → (p : Functor.base H₂ (Functor.base G x₁)
        ≡ Functor.base F (Functor.base H₁ x₁))
      → (q : Functor.base H₂ (Functor.base G y₁)
        ≡ Functor.base F (Functor.base H₁ y₁))
      → (f₁ : Category.Arrow C₁
        (Functor.base H₁ x₁)
        (Functor.base H₁ y₁))
      → Category.ArrowEqual D₂
        (WeakFunctor.map' H₂'
          (Functor.base G x₁)
          (Functor.base G y₁) p q
          (Functor.map F f₁))
        (Functor.map G
          (WeakFunctor.map H₁' x₁ y₁ f₁))

  map'
    : (x₁ y₁ : Category.Object D₁)
    → Functor.base H₂ (Functor.base G x₁)
      ≡ Functor.base F (Functor.base H₁ x₁)
    → Functor.base H₂ (Functor.base G y₁)
      ≡ Functor.base F (Functor.base H₁ y₁)
    → (f₁ : Category.Arrow C₁
      (Functor.base H₁ x₁)
      (Functor.base H₁ y₁))
    → {f₂ : Category.Arrow C₂
      (Functor.base H₂ (Functor.base G x₁))
      (Functor.base H₂ (Functor.base G y₁))}
    → Category.ArrowEqual' C₂ f₂ (Functor.map F f₁)
    → Category.ArrowEqual D₂
      (WeakFunctor.map H₂'
        (Functor.base G x₁)
        (Functor.base G y₁) f₂)
      (Functor.map G
        (WeakFunctor.map H₁' x₁ y₁ f₁))
  map' x₁ y₁ p q f₁ r
    = Category.arrow-trans D₂
      (WeakFunctor.map-equal'' H₂' x₂ y₂ refl p refl q r)
    $ map x₁ y₁ p q f₁
    where
      x₂ = Functor.base G x₁
      y₂ = Functor.base G y₁

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
  where

  module WeakFunctorSquareCompose
    (s : FunctorSquare H G I₁ I₂)
    (t : FunctorSquare G F J₁ J₂)
    (s' : WeakFunctorSquare G H I₁' I₂')
    (t' : WeakFunctorSquare F G J₁' J₂')
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
      → Category.ArrowEqual E₂
        (WeakFunctor.map' (weak-functor-compose I₂' J₂') x₂'' y₂'' p₂'' q₂'' f₂)
        (WeakFunctor.map' I₂' x₂'' y₂'' p₂' q₂'
          (WeakFunctor.map' J₂' x₂' y₂' p₂ q₂ f₂))
    map₂ _ _ refl refl refl refl refl refl _
      = Category.arrow-refl E₂

    map
      : (x₁ y₁ : Category.Object E₁)
      → (p : Functor.base (functor-compose' J₂ I₂) (Functor.base H x₁)
        ≡ Functor.base F (Functor.base (functor-compose' J₁ I₁) x₁))
      → (q : Functor.base (functor-compose' J₂ I₂) (Functor.base H y₁)
        ≡ Functor.base F (Functor.base (functor-compose' J₁ I₁) y₁))
      → (f₁ : Category.Arrow C₁
        (Functor.base (functor-compose' J₁ I₁) x₁)
        (Functor.base (functor-compose' J₁ I₁) y₁))
      → Category.ArrowEqual E₂
        (WeakFunctor.map'
          (weak-functor-compose I₂' J₂')
          (Functor.base H x₁)
          (Functor.base H y₁) p q
          (Functor.map F f₁))
        (Functor.map H
          (WeakFunctor.map (weak-functor-compose I₁' J₁') x₁ y₁ f₁))
    map x₁'' y₁'' p'' q'' f₁
      = Category.arrow-trans E₂ (map₂ x₂'' y₂'' p p' p'' q q' q'' f₂)
      $ Category.arrow-trans E₂ (WeakFunctor.map-equal' I₂' x₂'' y₂'' p' q'
        (WeakFunctorSquare.map t' x₁' y₁' p q f₁))
      $ WeakFunctorSquare.map s' x₁'' y₁'' p' q'
        (WeakFunctor.map J₁' x₁' y₁' f₁)
      where
        x₁' = Functor.base I₁ x₁''
        y₁' = Functor.base I₁ y₁''
        x₂'' = Functor.base H x₁''
        y₂'' = Functor.base H y₁''
        f₂ = Functor.map F f₁
        p = FunctorSquare.base t x₁'
        p' = FunctorSquare.base s x₁''
        q = FunctorSquare.base t y₁'
        q' = FunctorSquare.base s y₁''

  weak-functor-square-compose
    : FunctorSquare H G I₁ I₂
    → FunctorSquare G F J₁ J₂
    → WeakFunctorSquare G H I₁' I₂'
    → WeakFunctorSquare F G J₁' J₂'
    → WeakFunctorSquare F H
      (weak-functor-compose I₁' J₁')
      (weak-functor-compose I₂' J₂')
  weak-functor-square-compose s t s' t'
    = record {WeakFunctorSquareCompose s t s' t'}

