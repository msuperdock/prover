module Prover.Category.Dependent1.Maybe where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor; Dependent₁FunctorCompose;
    Dependent₁FunctorIdentity; Dependent₁FunctorSquare)
open import Prover.Category.Maybe
  using (category-maybe; functor-compose-maybe; functor-compose-maybe-eq;
    functor-identity-maybe; functor-identity-maybe-eq; functor-maybe;
    functor-square-maybe; functor-square-maybe-eq)

-- ## Dependent₁Category

module _
  {C : Category}
  where
  
  module Dependent₁CategoryMaybe
    (C' : Dependent₁Category C)
    where

    category
      : Category.Object C
      → Category
    category x
      = category-maybe
        (Dependent₁Category.category C' x)

    functor
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → Functor
        (category x)
        (category y)
    functor f
      = functor-maybe
        (Dependent₁Category.functor C' f)

    abstract

      functor-identity
        : (x : Category.Object C)
        → FunctorIdentity
          (functor (Category.identity C x))
      functor-identity x
        = functor-identity-maybe
          (Dependent₁Category.functor-identity C' x)
  
      functor-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → FunctorCompose
          (functor f)
          (functor g)
          (functor (Category.compose C f g))
      functor-compose f g
        = functor-compose-maybe
          (Dependent₁Category.functor-compose C' f g)

  dependent₁-category-maybe
    : Dependent₁Category C
    → Dependent₁Category C
  dependent₁-category-maybe C'
    = record {Dependent₁CategoryMaybe C'}

-- ## Dependent₁Functor

module _
  {C D : Category}
  {C' : Dependent₁Category C}
  {D' : Dependent₁Category D}
  {F : Functor C D}
  where

  module Dependent₁FunctorMaybe
    (F' : Dependent₁Functor C' D' F)
    where

    functor
      : (x : Category.Object C)
      → Functor
        (category-maybe (Dependent₁Category.category C' x))
        (category-maybe (Dependent₁Category.category D' (Functor.base F x)))
    functor x
      = functor-maybe
        (Dependent₁Functor.functor F' x)

    abstract

      functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → FunctorSquare
          (Dependent₁Category.functor (dependent₁-category-maybe C') f)
          (Dependent₁Category.functor (dependent₁-category-maybe D')
            (Functor.map F f))
          (functor x)
          (functor y)
      functor-square f
        = functor-square-maybe
          (Dependent₁Functor.functor-square F' f)

  dependent₁-functor-maybe
    : Dependent₁Functor C' D' F
    → Dependent₁Functor
      (dependent₁-category-maybe C')
      (dependent₁-category-maybe D') F
  dependent₁-functor-maybe F
    = record {Dependent₁FunctorMaybe F}

-- ## Dependent₁FunctorIdentity

module _
  {C : Category}
  {C' : Dependent₁Category C}
  {F : Functor C C}
  {F' : Dependent₁Functor C' C' F}
  where

  module Dependent₁FunctorIdentityMaybe
    (p : FunctorIdentity F)
    (p' : Dependent₁FunctorIdentity F')
    where

    functor
      : (x : Category.Object C)
      → FunctorIdentity
        (Dependent₁Functor.functor (dependent₁-functor-maybe F') x)
    functor x
      = functor-identity-maybe-eq
        (Dependent₁Category.category C')
        (FunctorIdentity.base p x)
        (Dependent₁FunctorIdentity.functor p' x)

  dependent₁-functor-identity-maybe
    : FunctorIdentity F
    → Dependent₁FunctorIdentity F'
    → Dependent₁FunctorIdentity
      (dependent₁-functor-maybe F')
  dependent₁-functor-identity-maybe p p'
    = record {Dependent₁FunctorIdentityMaybe p p'}

-- ## Dependent₁FunctorCompose

module _
  {C D E : Category}
  {C' : Dependent₁Category C}
  {D' : Dependent₁Category D}
  {E' : Dependent₁Category E}
  {F : Functor D E}
  {G : Functor C D}
  {H : Functor C E}
  {F' : Dependent₁Functor D' E' F}
  {G' : Dependent₁Functor C' D' G}
  {H' : Dependent₁Functor C' E' H}
  where

  module Dependent₁FunctorComposeMaybe
    (p : FunctorCompose F G H)
    (p' : Dependent₁FunctorCompose F' G' H')
    where

    functor
      : (x : Category.Object C)
      → FunctorCompose
        (Dependent₁Functor.functor (dependent₁-functor-maybe F')
          (Functor.base G x))
        (Dependent₁Functor.functor (dependent₁-functor-maybe G') x)
        (Dependent₁Functor.functor (dependent₁-functor-maybe H') x)
    functor x
      = functor-compose-maybe-eq
        (Dependent₁Category.category E')
        (FunctorCompose.base p x)
        (Dependent₁FunctorCompose.functor p' x)

  dependent₁-functor-compose-maybe
    : FunctorCompose F G H
    → Dependent₁FunctorCompose F' G' H'
    → Dependent₁FunctorCompose
      (dependent₁-functor-maybe F')
      (dependent₁-functor-maybe G')
      (dependent₁-functor-maybe H')
  dependent₁-functor-compose-maybe p p'
    = record {Dependent₁FunctorComposeMaybe p p'}

-- ## Dependent₁FunctorSquare

module _
  {C₁ C₂ D₁ D₂ : Category}
  {C₁' : Dependent₁Category C₁}
  {C₂' : Dependent₁Category C₂}
  {D₁' : Dependent₁Category D₁}
  {D₂' : Dependent₁Category D₂}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : Functor C₁ D₁}
  {H₂ : Functor C₂ D₂}
  {F' : Dependent₁Functor C₁' C₂' F}
  {G' : Dependent₁Functor D₁' D₂' G}
  {H₁' : Dependent₁Functor C₁' D₁' H₁}
  {H₂' : Dependent₁Functor C₂' D₂' H₂}
  where

  module Dependent₁FunctorSquareMaybe
    (s : FunctorSquare F G H₁ H₂)
    (s' : Dependent₁FunctorSquare F' G' H₁' H₂')
    where

    functor
      : (x₁ : Category.Object C₁)
      → FunctorSquare
        (Dependent₁Functor.functor (dependent₁-functor-maybe F') x₁)
        (Dependent₁Functor.functor (dependent₁-functor-maybe G')
          (Functor.base H₁ x₁))
        (Dependent₁Functor.functor (dependent₁-functor-maybe H₁') x₁)
        (Dependent₁Functor.functor (dependent₁-functor-maybe H₂')
          (Functor.base F x₁))
    functor x₁
      = functor-square-maybe-eq
        (Dependent₁Category.category D₂')
        (FunctorSquare.base s x₁)
        (Dependent₁FunctorSquare.functor s' x₁)

  dependent₁-functor-square-maybe
    : FunctorSquare F G H₁ H₂
    → Dependent₁FunctorSquare F' G' H₁' H₂'
    → Dependent₁FunctorSquare
      (dependent₁-functor-maybe F')
      (dependent₁-functor-maybe G')
      (dependent₁-functor-maybe H₁')
      (dependent₁-functor-maybe H₂')
  dependent₁-functor-square-maybe s s'
    = record {Dependent₁FunctorSquareMaybe s s'}

