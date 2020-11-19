module Prover.Category.Induced where

open import Prover.Category
  using (Category; Functor; Precategory; Prefunctor)
open import Prover.Category.Split
  using (SplitPrefunctor)
open import Prover.Prelude

-- ## Category

module _
  {C : Category}
  {D : Precategory}
  where

  module CategoryInduced
    (F : SplitPrefunctor C D)
    where

    open Precategory D public
      using (Object; Arrow; ArrowEqual; identity; compose) 

    abstract

      arrow-refl
        : {x y : Object}
        → {f : Arrow x y}
        → ArrowEqual f f
      arrow-refl
        = Precategory.arrow-refl D

      arrow-sym
        : {x y : Object}
        → {f₁ f₂ : Arrow x y}
        → ArrowEqual f₁ f₂
        → ArrowEqual f₂ f₁
      arrow-sym
        = Precategory.arrow-sym D

      arrow-trans
        : {x y : Object}
        → {f₁ f₂ f₃ : Arrow x y}
        → ArrowEqual f₁ f₂
        → ArrowEqual f₂ f₃
        → ArrowEqual f₁ f₃
      arrow-trans
        = Precategory.arrow-trans D

      simplify
        : {x y : Object}
        → Arrow x y
        → Arrow x y
      simplify {x = x} {y = y} f
        = SplitPrefunctor.map F
          (SplitPrefunctor.base-unbase F x)
          (SplitPrefunctor.base-unbase F y)
          (SplitPrefunctor.unmap F f)

      simplify-equal
        : {x y : Object}
        → (f : Arrow x y)
        → ArrowEqual
          (simplify f) f
      simplify-equal
        = SplitPrefunctor.map-unmap F

      compose-equal
        : {x y z : Object}
        → {f₁ f₂ : Arrow y z}
        → {g₁ g₂ : Arrow x y}
        → ArrowEqual f₁ f₂
        → ArrowEqual g₁ g₂
        → ArrowEqual
          (compose f₁ g₁)
          (compose f₂ g₂)
      compose-equal {x = x} {z = z} {f₁ = f₁} {f₂ = f₂} {g₁ = g₁} {g₂ = g₂} s t
        = arrow-trans (arrow-sym
          (SplitPrefunctor.map-unmap F (compose f₁ g₁)))
        $ arrow-trans (SplitPrefunctor.map-equal F p r
          (SplitPrefunctor.unmap-compose F f₁ g₁))
        $ arrow-trans (SplitPrefunctor.map-equal F p r
          (Category.compose-equal C s' t'))
        $ arrow-trans (arrow-sym (SplitPrefunctor.map-equal F p r
          (SplitPrefunctor.unmap-compose F f₂ g₂)))
        $ SplitPrefunctor.map-unmap F (compose f₂ g₂)
        where
          p = SplitPrefunctor.base-unbase F x
          r = SplitPrefunctor.base-unbase F z
          s' = SplitPrefunctor.unmap-equal F s
          t' = SplitPrefunctor.unmap-equal F t

      precompose
        : {x y : Object}
        → (f : Arrow x y)
        → ArrowEqual
          (compose f (identity x)) f
      precompose {x = x} {y = y} f
        = arrow-trans (arrow-sym
          (SplitPrefunctor.map-unmap F (compose f (identity x))))
        $ arrow-trans (SplitPrefunctor.map-equal F p q
          (SplitPrefunctor.unmap-compose F f (identity x)))
        $ arrow-trans (SplitPrefunctor.map-equal F p q
          (Category.compose-equal C (Category.arrow-refl C) p'))
        $ arrow-trans (SplitPrefunctor.map-equal F p q
          (Category.precompose C f'))
        $ SplitPrefunctor.map-unmap F f
        where
          f' = SplitPrefunctor.unmap F f
          p = SplitPrefunctor.base-unbase F x
          q = SplitPrefunctor.base-unbase F y
          p' = SplitPrefunctor.unmap-identity F x

      postcompose
        : {x y : Object}
        → (f : Arrow x y)
        → ArrowEqual
          (compose (identity y) f) f
      postcompose {x = x} {y = y} f
        = arrow-trans (arrow-sym
          (SplitPrefunctor.map-unmap F (compose (identity y) f)))
        $ arrow-trans (SplitPrefunctor.map-equal F p q
          (SplitPrefunctor.unmap-compose F (identity y) f))
        $ arrow-trans (SplitPrefunctor.map-equal F p q
          (Category.compose-equal C q' (Category.arrow-refl C)))
        $ arrow-trans (SplitPrefunctor.map-equal F p q
          (Category.postcompose C f'))
        $ SplitPrefunctor.map-unmap F f
        where
          f' = SplitPrefunctor.unmap F f
          p = SplitPrefunctor.base-unbase F x
          q = SplitPrefunctor.base-unbase F y
          q' = SplitPrefunctor.unmap-identity F y

      associative
        : {w x y z : Object}
        → (f : Arrow y z)
        → (g : Arrow x y)
        → (h : Arrow w x)
        → ArrowEqual
          (compose (compose f g) h)
          (compose f (compose g h))
      associative {w = w} {z = z} f g h
        = arrow-trans (arrow-sym
          (SplitPrefunctor.map-unmap F (compose (compose f g) h)))
        $ arrow-trans (SplitPrefunctor.map-equal F p q
          (SplitPrefunctor.unmap-compose F (compose f g) h))
        $ arrow-trans (SplitPrefunctor.map-equal F p q
          (Category.compose-equal C r (Category.arrow-refl C)))
        $ arrow-trans (SplitPrefunctor.map-equal F p q
          (Category.associative C f' g' h'))
        $ arrow-trans (arrow-sym (SplitPrefunctor.map-equal F p q
          (Category.compose-equal C (Category.arrow-refl C) s)))
        $ arrow-trans (arrow-sym (SplitPrefunctor.map-equal F p q
          (SplitPrefunctor.unmap-compose F f (compose g h))))
        $ SplitPrefunctor.map-unmap F (compose f (compose g h))
        where
          f' = SplitPrefunctor.unmap F f
          g' = SplitPrefunctor.unmap F g
          h' = SplitPrefunctor.unmap F h
          p = SplitPrefunctor.base-unbase F w
          q = SplitPrefunctor.base-unbase F z
          r = SplitPrefunctor.unmap-compose F f g
          s = SplitPrefunctor.unmap-compose F g h

  category-induced
    : SplitPrefunctor C D
    → Category
  category-induced F
    = record {CategoryInduced F}

-- ## Functor

functor-induced
  : {C : Category}
  → {D : Precategory}
  → (F : SplitPrefunctor C D)
  → Functor
    (category-induced F) C
functor-induced F
  = record {Prefunctor (SplitPrefunctor.prefunctor F)}

