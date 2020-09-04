module Prover.Category.Dependent1 where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare; functor-compose'; functor-compose-to-equal;
    functor-identity'; functor-identity-to-equal; functor-square-compose;
    functor-square-identity; functor-square-to-equal)
open import Prover.Prelude

-- ## Dependent₁Category

record Dependent₁Category
  (C : Category)
  : Set₁
  where

  field

    category
      : Category.Object C
      → Category

  Object
    : Category.Object C
    → Set
  Object x
    = Category.Object
      (category x)

  Arrow
    : (x : Category.Object C)
    → Object x
    → Object x
    → Set
  Arrow x
    = Category.Arrow
      (category x)

  identity
    : (x : Category.Object C)
    → (x' : Object x)
    → Arrow x x' x'
  identity x
    = Category.identity
      (category x)

  compose
    : (x : Category.Object C)
    → {x' y' z' : Object x}
    → Arrow x y' z'
    → Arrow x x' y'
    → Arrow x x' z'
  compose x
    = Category.compose
      (category x)

  compose-eq
    : (x : Category.Object C)
    → {x' y₁' y₂' z' : Object x}
    → y₁' ≡ y₂'
    → Arrow x y₂' z'
    → Arrow x x' y₁'
    → Arrow x x' z'
  compose-eq x
    = Category.compose-eq'
      (category x)

  precompose
    : (x : Category.Object C)
    → {x' y' : Object x}
    → (f : Arrow x x' y')
    → compose x f (identity x x') ≡ f
  precompose x
    = Category.precompose
      (category x)

  postcompose
    : (x : Category.Object C)
    → {x' y' : Object x}
    → (f : Arrow x x' y')
    → compose x (identity x y') f ≡ f
  postcompose x
    = Category.postcompose
      (category x)

  associative
    : (x : Category.Object C)
    → {w' x' y' z' : Object x}
    → (f : Arrow x y' z')
    → (g : Arrow x x' y')
    → (h : Arrow x w' x')
    → compose x (compose x f g) h ≡ compose x f (compose x g h)
  associative x
    = Category.associative
      (category x)

  field

    functor
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → Functor
        (category x)
        (category y)

    functor-identity
      : (x : Category.Object C)
      → FunctorIdentity
        (functor (Category.identity C x))

    functor-compose
      : {x y z : Category.Object C}
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → FunctorCompose
        (functor f)
        (functor g)
        (functor (Category.compose C f g))

  base
    : {x y : Category.Object C}
    → Category.Arrow C x y
    → Object x
    → Object y
  base f
    = Functor.base
      (functor f)
      
  base-eq
    : {x₁ x₂ y₁ y₂ : Category.Object C}
    → {x₁' : Object x₁}
    → {x₂' : Object x₂}
    → {f₁ : Category.Arrow C x₁ y₁}
    → {f₂ : Category.Arrow C x₂ y₂}
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → x₁' ≅ x₂'
    → f₁ ≅ f₂
    → base f₁ x₁' ≅ base f₂ x₂'
  base-eq refl refl refl refl
    = refl

  base-identity
    : (x : Category.Object C)
    → (x' : Object x)
    → base (Category.identity C x) x' ≡ x'
  base-identity x
    = FunctorIdentity.base
      (functor-identity x)

  base-compose
    : {x y z : Category.Object C}
    → (f : Category.Arrow C y z)
    → (g : Category.Arrow C x y)
    → (x' : Object x)
    → base (Category.compose C f g) x' ≡ base f (base g x')
  base-compose f g
    = FunctorCompose.base
      (functor-compose f g)

  map
    : {x y : Category.Object C}
    → {x' y' : Object x}
    → (f : Category.Arrow C x y)
    → Arrow x x' y'
    → Arrow y (base f x') (base f y')
  map f
    = Functor.map
      (functor f)

  map-identity
    : (x : Category.Object C)
    → {x' y' : Object x}
    → (f : Arrow x x' y')
    → map (Category.identity C x) f ≅ f
  map-identity x
    = FunctorIdentity.map
      (functor-identity x)

  map-identity'
    : {x y : Category.Object C}
    → (f : Category.Arrow C x y)
    → (x' : Object x)
    → map f (identity x x') ≡ identity y (base f x')
  map-identity' f
    = Functor.map-identity
      (functor f)

  map-compose
    : {x y z : Category.Object C}
    → {x' y' : Object x}
    → (f : Category.Arrow C y z)
    → (g : Category.Arrow C x y)
    → (f' : Arrow x x' y')
    → map (Category.compose C f g) f' ≅ map f (map g f')
  map-compose f g
    = FunctorCompose.map
      (functor-compose f g)

  map-compose-eq'
    : {x y : Category.Object C}
    → {x' y₁' y₂' z' : Object x}
    → (f : Category.Arrow C x y)
    → (p : y₁' ≡ y₂')
    → (q : base f y₁' ≡ base f y₂')
    → (f' : Arrow x y₂' z')
    → (g' : Arrow x x' y₁')
    → map f (compose-eq x p f' g') ≡ compose-eq y q (map f f') (map f g')
  map-compose-eq' f
    = Functor.map-compose-eq
      (functor f)

-- ## Dependent₁Functor

-- ### Definition

record Dependent₁Functor
  {C D : Category}
  (C' : Dependent₁Category C)
  (D' : Dependent₁Category D)
  : Set
  where

  no-eta-equality

  field

    functor
      : Functor C D

  open Functor functor public

  field

    functor'
      : (x : Category.Object C)
      → Functor
        (Dependent₁Category.category C' x)
        (Dependent₁Category.category D' (base x))

  base'
    : (x : Category.Object C)
    → Dependent₁Category.Object C' x
    → Dependent₁Category.Object D' (base x)
  base' x
    = Functor.base
      (functor' x)

  map'
    : (x : Category.Object C)
    → {x' y' : Dependent₁Category.Object C' x}
    → Dependent₁Category.Arrow C' x x' y'
    → Dependent₁Category.Arrow D' (base x) (base' x x') (base' x y')
  map' x
    = Functor.map
      (functor' x)

  map-identity'
    : (x : Category.Object C)
    → (x' : Dependent₁Category.Object C' x)
    → map' x (Dependent₁Category.identity C' x x')
      ≡ Dependent₁Category.identity D' (base x) (base' x x')
  map-identity' x
    = Functor.map-identity
      (functor' x)

  map-compose-eq'
    : (x : Category.Object C)
    → {x' y₁' y₂' z' : Dependent₁Category.Object C' x}
    → (p : y₁' ≡ y₂')
    → (q : base' x y₁' ≡ base' x y₂')
    → (f : Dependent₁Category.Arrow C' x y₂' z')
    → (g : Dependent₁Category.Arrow C' x x' y₁')
    → map' x (Dependent₁Category.compose-eq C' x p f g)
      ≡ Dependent₁Category.compose-eq D' (base x) q (map' x f) (map' x g)
  map-compose-eq' x
    = Functor.map-compose-eq
      (functor' x)

  field

    functor-square
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → FunctorSquare
        (Dependent₁Category.functor C' f)
        (Dependent₁Category.functor D' (map f))
        (functor' x)
        (functor' y)

  base-commutative
    : {x y : Category.Object C}
    → (f : Category.Arrow C x y)
    → (x' : Dependent₁Category.Object C' x)
    → base' y (Dependent₁Category.base C' f x')
      ≅ Dependent₁Category.base D' (map f) (base' x x')
  base-commutative f
    = FunctorSquare.base
      (functor-square f)

  map-commutative
    : {x y : Category.Object C}
    → {x' y' : Dependent₁Category.Object C' x}
    → (f : Category.Arrow C x y)
    → (f' : Dependent₁Category.Arrow C' x x' y')
    → map' y (Dependent₁Category.map C' f f')
      ≅ Dependent₁Category.map D' (map f) (map' x f')
  map-commutative f
    = FunctorSquare.map
      (functor-square f)

-- ### Identity

module _
  {C : Category}
  where

  module Dependent₁FunctorIdentity'
    (C' : Dependent₁Category C)
    where

    functor
      : Functor C C
    functor
      = functor-identity' C

    open Functor functor

    functor'
      : (x : Category.Object C)
      → Functor
        (Dependent₁Category.category C' x)
        (Dependent₁Category.category C' (base x))
    functor' x
      = functor-identity'
        (Dependent₁Category.category C' x)

    abstract

      functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → FunctorSquare
          (Dependent₁Category.functor C' f)
          (Dependent₁Category.functor C' (map f))
          (functor' x)
          (functor' y)
      functor-square f
        = functor-square-identity
          (Dependent₁Category.functor C' f)

  dependent₁-functor-identity
    : (C' : Dependent₁Category C)
    → Dependent₁Functor C' C'
  dependent₁-functor-identity F
    = record {Dependent₁FunctorIdentity' F}

-- ### Compose

module _
  {C D E : Category}
  {C' : Dependent₁Category C}
  {D' : Dependent₁Category D}
  {E' : Dependent₁Category E}
  where

  module Dependent₁FunctorCompose'
    (F : Dependent₁Functor D' E')
    (G : Dependent₁Functor C' D')
    where

    functor
      : Functor C E
    functor
      = functor-compose'
        (Dependent₁Functor.functor F)
        (Dependent₁Functor.functor G)

    open Functor functor

    functor'
      : (x : Category.Object C)
      → Functor
        (Dependent₁Category.category C' x)
        (Dependent₁Category.category E' (base x))
    functor' x
      = functor-compose'
        (Dependent₁Functor.functor' F (Dependent₁Functor.base G x))
        (Dependent₁Functor.functor' G x)

    abstract

      functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → FunctorSquare
          (Dependent₁Category.functor C' f)
          (Dependent₁Category.functor E' (map f))
          (functor' x)
          (functor' y)
      functor-square f
        = functor-square-compose
          (Dependent₁Functor.functor-square F (Dependent₁Functor.map G f))
          (Dependent₁Functor.functor-square G f)

  dependent₁-functor-compose
    : Dependent₁Functor D' E'
    → Dependent₁Functor C' D'
    → Dependent₁Functor C' E'
  dependent₁-functor-compose F G
    = record {Dependent₁FunctorCompose' F G}

-- ## Dependent₁FunctorEqual

record Dependent₁FunctorEqual
  {C D : Category}
  {C' : Dependent₁Category C}
  {D' : Dependent₁Category D}
  (F₁ F₂ : Dependent₁Functor C' D')
  : Set
  where

  field

    functor
      : FunctorEqual
        (Dependent₁Functor.functor F₁)
        (Dependent₁Functor.functor F₂)

  open FunctorEqual functor public

  field

    functor'
      : (x : Category.Object C)
      → FunctorEqual
        (Dependent₁Functor.functor' F₁ x)
        (Dependent₁Functor.functor' F₂ x)

  base'
    : (x : Category.Object C)
    → (x' : Dependent₁Category.Object C' x)
    → Dependent₁Functor.base' F₁ x x' ≅ Dependent₁Functor.base' F₂ x x'
  base' x
    = FunctorEqual.base
      (functor' x)
  
  map'
    : (x : Category.Object C)
    → {x' y' : Dependent₁Category.Object C' x}
    → (f : Dependent₁Category.Arrow C' x x' y')
    → Dependent₁Functor.map' F₁ x f ≅ Dependent₁Functor.map' F₂ x f
  map' x
    = FunctorEqual.map
      (functor' x)

-- ## Dependent₁FunctorIdentity

-- ### Definition

record Dependent₁FunctorIdentity
  {C : Category}
  {C' : Dependent₁Category C}
  (F : Dependent₁Functor C' C')
  : Set
  where

  field

    functor
      : FunctorIdentity
        (Dependent₁Functor.functor F)
        
  open FunctorIdentity functor public

  field

    functor'
      : (x : Category.Object C)
      → FunctorIdentity
        (Dependent₁Functor.functor' F x)

-- ### Conversion

module _
  {C : Category}
  {C' : Dependent₁Category C}
  {F : Dependent₁Functor C' C'}
  where

  module Dependent₁FunctorIdentityToEqual
    (p : Dependent₁FunctorIdentity F)
    where

    functor
      : FunctorEqual
        (Dependent₁Functor.functor F)
        (Dependent₁Functor.functor (dependent₁-functor-identity C'))
    functor
      = functor-identity-to-equal
        (Dependent₁FunctorIdentity.functor p)

    functor'
      : (x : Category.Object C)
      → FunctorEqual
        (Dependent₁Functor.functor' F x)
        (Dependent₁Functor.functor' (dependent₁-functor-identity C') x)
    functor' x
      = functor-identity-to-equal
        (Dependent₁FunctorIdentity.functor' p x)

  dependent₁-functor-identity-to-equal
    : Dependent₁FunctorIdentity F
    → Dependent₁FunctorEqual F (dependent₁-functor-identity C')
  dependent₁-functor-identity-to-equal p
    = record {Dependent₁FunctorIdentityToEqual p}

-- ## Dependent₁FunctorCompose

-- ### Definition

record Dependent₁FunctorCompose
  {C D E : Category}
  {C' : Dependent₁Category C}
  {D' : Dependent₁Category D}
  {E' : Dependent₁Category E}
  (F : Dependent₁Functor D' E')
  (G : Dependent₁Functor C' D')
  (H : Dependent₁Functor C' E')
  : Set
  where

  field
    
    functor
      : FunctorCompose
        (Dependent₁Functor.functor F)
        (Dependent₁Functor.functor G)
        (Dependent₁Functor.functor H)

  open FunctorCompose functor public

  field

    functor'
      : (x : Category.Object C)
      → FunctorCompose
        (Dependent₁Functor.functor' F (Dependent₁Functor.base G x))
        (Dependent₁Functor.functor' G x)
        (Dependent₁Functor.functor' H x)

-- ### Conversion

module _
  {C D E : Category}
  {C' : Dependent₁Category C}
  {D' : Dependent₁Category D}
  {E' : Dependent₁Category E}
  {F : Dependent₁Functor D' E'}
  {G : Dependent₁Functor C' D'}
  {H : Dependent₁Functor C' E'}
  where

  module Dependent₁FunctorComposeToEqual
    (p : Dependent₁FunctorCompose F G H)
    where

    functor
      : FunctorEqual
        (Dependent₁Functor.functor H)
        (Dependent₁Functor.functor (dependent₁-functor-compose F G))
    functor
      = functor-compose-to-equal
        (Dependent₁FunctorCompose.functor p)

    functor'
      : (x : Category.Object C)
      → FunctorEqual
        (Dependent₁Functor.functor' H x)
        (Dependent₁Functor.functor' (dependent₁-functor-compose F G) x)
    functor' x
      = functor-compose-to-equal
        (Dependent₁FunctorCompose.functor' p x)

  dependent₁-functor-compose-to-equal
    : Dependent₁FunctorCompose F G H
    → Dependent₁FunctorEqual H (dependent₁-functor-compose F G)
  dependent₁-functor-compose-to-equal p
    = record {Dependent₁FunctorComposeToEqual p}

-- ## Dependent₁FunctorSquare

-- ### Definition

record Dependent₁FunctorSquare
  {C₁ C₂ D₁ D₂ : Category}
  {C₁' : Dependent₁Category C₁}
  {C₂' : Dependent₁Category C₂}
  {D₁' : Dependent₁Category D₁}
  {D₂' : Dependent₁Category D₂}
  (F : Dependent₁Functor C₁' C₂')
  (G : Dependent₁Functor D₁' D₂')
  (H₁ : Dependent₁Functor C₁' D₁')
  (H₂ : Dependent₁Functor C₂' D₂')
  : Set
  where

  field
 
    functor
      : FunctorSquare
        (Dependent₁Functor.functor F)
        (Dependent₁Functor.functor G)
        (Dependent₁Functor.functor H₁)
        (Dependent₁Functor.functor H₂)

  open FunctorSquare functor public

  field

    functor'
      : (x₁ : Category.Object C₁)
      → FunctorSquare
        (Dependent₁Functor.functor' F x₁)
        (Dependent₁Functor.functor' G (Dependent₁Functor.base H₁ x₁))
        (Dependent₁Functor.functor' H₁ x₁)
        (Dependent₁Functor.functor' H₂ (Dependent₁Functor.base F x₁))

-- ### Conversion

module _
  {C₁ C₂ D₁ D₂ : Category}
  {C₁' : Dependent₁Category C₁}
  {C₂' : Dependent₁Category C₂}
  {D₁' : Dependent₁Category D₁}
  {D₂' : Dependent₁Category D₂}
  {F : Dependent₁Functor C₁' C₂'}
  {G : Dependent₁Functor D₁' D₂'}
  {H₁ : Dependent₁Functor C₁' D₁'}
  {H₂ : Dependent₁Functor C₂' D₂'}
  where

  module Dependent₁FunctorSquareToEqual
    (s : Dependent₁FunctorSquare F G H₁ H₂)
    where

    functor
      : FunctorEqual
        (Dependent₁Functor.functor (dependent₁-functor-compose H₂ F))
        (Dependent₁Functor.functor (dependent₁-functor-compose G H₁))
    functor
      = functor-square-to-equal
        (Dependent₁FunctorSquare.functor s)

    functor'
      : (x₁ : Category.Object C₁)
      → FunctorEqual
        (Dependent₁Functor.functor' (dependent₁-functor-compose H₂ F) x₁)
        (Dependent₁Functor.functor' (dependent₁-functor-compose G H₁) x₁)
    functor' x₁
      = functor-square-to-equal
        (Dependent₁FunctorSquare.functor' s x₁)

  dependent₁-functor-square-to-equal
    : Dependent₁FunctorSquare F G H₁ H₂
    → Dependent₁FunctorEqual
      (dependent₁-functor-compose H₂ F)
      (dependent₁-functor-compose G H₁)
  dependent₁-functor-square-to-equal s
    = record {Dependent₁FunctorSquareToEqual s}

