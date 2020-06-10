module Prover.Category where

open import Prover.Prelude

-- ## Category

record Category
  : Set₁
  where

  no-eta-equality

  field

    Object
      : Set

    Arrow
      : Object
      → Object
      → Set

    identity
      : (x : Object)
      → Arrow x x

    compose
      : {x y z : Object}
      → Arrow y z
      → Arrow x y
      → Arrow x z

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose f (identity x) ≡ f

    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose (identity y) f ≡ f

    associative
      : {w x y z : Object}
      → (f : Arrow y z)
      → (g : Arrow x y)
      → (h : Arrow w x)
      → compose (compose f g) h ≡ compose f (compose g h)

  arrow
    : {x₁ x₂ y₁ y₂ : Object}
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → Arrow x₂ y₂
    → Arrow x₁ y₁
  arrow refl refl
    = id

  arrow-eq
    : {x₁ x₂ y₁ y₂ : Object}
    → (p : x₁ ≡ x₂)
    → (q : y₁ ≡ y₂)
    → (f₂ : Arrow x₂ y₂)
    → arrow p q f₂ ≅ f₂
  arrow-eq refl refl _
    = refl

  compose-eq
    : {x y₁ y₂ z : Object}
    → y₁ ≡ y₂
    → Arrow y₂ z
    → Arrow x y₁
    → Arrow x z
  compose-eq refl
    = compose

-- ## Functor

-- ### Definition

record Functor
  (C D : Category)
  : Set
  where

  no-eta-equality

  field
    
    base
      : Category.Object C
      → Category.Object D

    map
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → Category.Arrow D (base x) (base y)

    map-identity
      : (x : Category.Object C)
      → map (Category.identity C x) ≡ Category.identity D (base x)

    map-compose
      : {x y z : Category.Object C}
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → map (Category.compose C f g) ≡ Category.compose D (map f) (map g)

  map-compose-eq
    : {x y₁ y₂ z : Category.Object C}
    → (p : y₁ ≡ y₂)
    → (q : base y₁ ≡ base y₂)
    → (f : Category.Arrow C y₂ z)
    → (g : Category.Arrow C x y₁)
    → map (Category.compose-eq C p f g)
      ≡ Category.compose-eq D q (map f) (map g)
  map-compose-eq refl refl
    = map-compose

-- ### Identity

module FunctorIdentity'
  (C : Category)
  where

  base
    : Category.Object C
    → Category.Object C
  base
    = id

  map
    : {x y : Category.Object C}
    → Category.Arrow C x y
    → Category.Arrow C (base x) (base y)
  map
    = id

  abstract

    map-identity
      : (x : Category.Object C)
      → map (Category.identity C x) ≡ Category.identity C (base x)
    map-identity _
      = refl
  
    map-compose
      : {x y z : Category.Object C}
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → map (Category.compose C f g) ≡ Category.compose C (map f) (map g)
    map-compose _ _
      = refl

functor-identity'
  : (C : Category)
  → Functor C C
functor-identity' C
  = record {FunctorIdentity' C}

-- ### Compose

module _
  {C D E : Category}
  where

  module FunctorCompose'
    (F : Functor D E)
    (G : Functor C D)
    where

    base
      : Category.Object C
      → Category.Object E
    base
      = Functor.base F
      ∘ Functor.base G

    map
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → Category.Arrow E (base x) (base y)
    map
      = Functor.map F
      ∘ Functor.map G

    abstract

      map-identity
        : (x : Category.Object C)
        → map (Category.identity C x) ≡ Category.identity E (base x)
      map-identity x
        with Functor.map G (Category.identity C x)
        | Functor.map-identity G x
      ... | _ | refl
        = Functor.map-identity F
          (Functor.base G x)
  
      map-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → map (Category.compose C f g) ≡ Category.compose E (map f) (map g)
      map-compose f g
        with Functor.map G (Category.compose C f g)
        | Functor.map-compose G f g
      ... | _ | refl
        = Functor.map-compose F
          (Functor.map G f)
          (Functor.map G g)

  functor-compose'
    : Functor D E 
    → Functor C D
    → Functor C E
  functor-compose' F G
    = record {FunctorCompose' F G}

-- ## FunctorEqual

-- ### Definition

record FunctorEqual
  {C D₁ D₂ : Category}
  (F₁ : Functor C D₁)
  (F₂ : Functor C D₂)
  : Set
  where

  field

    base
      : (x : Category.Object C)
      → Functor.base F₁ x ≅ Functor.base F₂ x
  
    map
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → Functor.map F₁ f ≅ Functor.map F₂ f

-- ### Reflexivity

module _
  {C D : Category}
  where

  module FunctorRefl
    (F : Functor C D)
    where
  
    base
      : (x : Category.Object C)
      → Functor.base F x ≅ Functor.base F x
    base _
      = refl
  
    map
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → Functor.map F f ≅ Functor.map F f
    map _
      = refl
  
  functor-refl
    : {F : Functor C D}
    → FunctorEqual F F
  functor-refl {F = F}
    = record {FunctorRefl F}

-- ### Symmetry

module _
  {C D₁ D₂ : Category}
  {F₁ : Functor C D₁}
  {F₂ : Functor C D₂}
  where

  module FunctorSym
    (p : FunctorEqual F₁ F₂)
    where
  
    base
      : (x : Category.Object C)
      → Functor.base F₂ x ≅ Functor.base F₁ x
    base x
      = sym (FunctorEqual.base p x)
  
    map
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → Functor.map F₂ f ≅ Functor.map F₁ f
    map f
      = sym (FunctorEqual.map p f)
  
  functor-sym
    : FunctorEqual F₁ F₂
    → FunctorEqual F₂ F₁
  functor-sym p
    = record {FunctorSym p}

-- ### Transitivity

module _
  {C D₁ D₂ D₃ : Category}
  {F₁ : Functor C D₁}
  {F₂ : Functor C D₂}
  {F₃ : Functor C D₃}
  where

  module FunctorTrans
    (p₁ : FunctorEqual F₁ F₂)
    (p₂ : FunctorEqual F₂ F₃)
    where
  
    base
      : (x : Category.Object C)
      → Functor.base F₁ x ≅ Functor.base F₃ x
    base x
      = trans
        (FunctorEqual.base p₁ x)
        (FunctorEqual.base p₂ x)
  
    map
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → Functor.map F₁ f ≅ Functor.map F₃ f
    map f
      = trans
        (FunctorEqual.map p₁ f)
        (FunctorEqual.map p₂ f)
  
  functor-trans
    : FunctorEqual F₁ F₂
    → FunctorEqual F₂ F₃
    → FunctorEqual F₁ F₃
  functor-trans p₁ p₂
    = record {FunctorTrans p₁ p₂}

-- ## FunctorIdentity

-- ### Definition

record FunctorIdentity
  {C₁ C₂ : Category}
  (F : Functor C₁ C₂)
  : Set
  where

  field

    base
      : (x₁ : Category.Object C₁)
      → Functor.base F x₁ ≅ x₁

    map
      : {x₁ y₁ : Category.Object C₁}
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Functor.map F f₁ ≅ f₁

-- ### Conversion

module _
  {C₁ C₂ : Category}
  {F : Functor C₁ C₂}
  where

  functor-identity-to-equal
    : FunctorIdentity F
    → FunctorEqual F (functor-identity' C₁)
  functor-identity-to-equal p
    = record {FunctorIdentity p}
  
  functor-identity-from-equal
    : FunctorEqual F (functor-identity' C₁)
    → FunctorIdentity F
  functor-identity-from-equal p
    = record {FunctorEqual p}

-- ## FunctorCompose

-- ### Definition

record FunctorCompose
  {C D E₁ E₂ : Category}
  (F : Functor D E₁)
  (G : Functor C D)
  (H : Functor C E₂)
  : Set
  where

  field

    base
      : (x : Category.Object C)
      → Functor.base H x ≅ Functor.base F (Functor.base G x)

    map
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → Functor.map H f ≅ Functor.map F (Functor.map G f)

-- ### Conversion

module _
  {C D E₁ E₂ : Category}
  {F : Functor D E₁}
  {G : Functor C D}
  {H : Functor C E₂}
  where

  functor-compose-to-equal
    : FunctorCompose F G H
    → FunctorEqual H (functor-compose' F G)
  functor-compose-to-equal p
    = record {FunctorCompose p}
  
  functor-compose-from-equal
    : FunctorEqual H (functor-compose' F G)
    → FunctorCompose F G H
  functor-compose-from-equal p
    = record {FunctorEqual p}

-- ## FunctorSquare

-- ### Definition

record FunctorSquare
  {C₁ C₂ D₁ D₂ D₃ : Category}
  (F : Functor C₁ C₂)
  (G : Functor D₁ D₃)
  (H₁ : Functor C₁ D₁)
  (H₂ : Functor C₂ D₂)
  : Set
  where

  field

    base
      : (x₁ : Category.Object C₁)
      → Functor.base H₂ (Functor.base F x₁) 
        ≅ Functor.base G (Functor.base H₁ x₁)
  
    map
      : {x₁ y₁ : Category.Object C₁}
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Functor.map H₂ (Functor.map F f₁)
        ≅ Functor.map G (Functor.map H₁ f₁)

-- ### Conversion

module _
  {C₁ C₂ D₁ D₂ D₃ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₃}
  {H₁ : Functor C₁ D₁}
  {H₂ : Functor C₂ D₂}
  where

  functor-square-to-equal
    : FunctorSquare F G H₁ H₂
    → FunctorEqual (functor-compose' H₂ F) (functor-compose' G H₁)
  functor-square-to-equal s
    = record {FunctorSquare s}
  
  functor-square-from-equal
    : FunctorEqual (functor-compose' H₂ F) (functor-compose' G H₁)
    → FunctorSquare F G H₁ H₂
  functor-square-from-equal p
    = record {FunctorEqual p}

-- ### Transpose

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : Functor C₁ D₁}
  {H₂ : Functor C₂ D₂}
  where

  module FunctorSquareTranspose
    (s : FunctorSquare F G H₁ H₂)
    where

    base
      : (x₁ : Category.Object C₁)
      → Functor.base G (Functor.base H₁ x₁) 
        ≅ Functor.base H₂ (Functor.base F x₁)
    base x₁
      = sym (FunctorSquare.base s x₁)
  
    map
      : {x₁ y₁ : Category.Object C₁}
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Functor.map G (Functor.map H₁ f₁)
        ≅ Functor.map H₂ (Functor.map F f₁)
    map f₁
      = sym (FunctorSquare.map s f₁)

  functor-square-transpose
    : FunctorSquare F G H₁ H₂
    → FunctorSquare H₁ H₂ F G
  functor-square-transpose s
    = record {FunctorSquareTranspose s}

-- ### Identity

module _
  {C₁ C₂ : Category}
  where

  module FunctorSquareIdentity
    (F : Functor C₁ C₂)
    where

    base
      : (x₁ : Category.Object C₁)
      → Functor.base (functor-identity' C₂) (Functor.base F x₁) 
        ≅ Functor.base F (Functor.base (functor-identity' C₁) x₁)
    base _
      = refl
  
    map
      : {x₁ y₁ : Category.Object C₁}
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Functor.map (functor-identity' C₂) (Functor.map F f₁)
        ≅ Functor.map F (Functor.map (functor-identity' C₁) f₁)
    map _
      = refl

  functor-square-identity
    : (F : Functor C₁ C₂)
    → FunctorSquare F F
      (functor-identity' C₁)
      (functor-identity' C₂)
  functor-square-identity F
    = record {FunctorSquareIdentity F}

  functor-square-identity-eq
    : {F G : Functor C₁ C₂}
    → FunctorEqual F G
    → FunctorSquare F G
      (functor-identity' C₁)
      (functor-identity' C₂)
  functor-square-identity-eq p
    = record {FunctorEqual p}

functor-square-identity'
  : {C D : Category}
  → (F : Functor C D)
  → FunctorSquare
    (functor-identity' C)
    (functor-identity' D) F F
functor-square-identity' F
  = functor-square-transpose
    (functor-square-identity F)

-- ### Compose

module _
  {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H : Functor E₁ E₂}
  {I₁ : Functor D₁ E₁}
  {I₂ : Functor D₂ E₂}
  {J₁ : Functor C₁ D₁}
  {J₂ : Functor C₂ D₂}
  where

  module FunctorSquareCompose
    (s : FunctorSquare G H I₁ I₂)
    (t : FunctorSquare F G J₁ J₂)
    where

    base
      : (x₁ : Category.Object C₁)
      → Functor.base (functor-compose' I₂ J₂) (Functor.base F x₁) 
        ≅ Functor.base H (Functor.base (functor-compose' I₁ J₁) x₁)
    base x₁
      with Functor.base J₂ (Functor.base F x₁)
      | FunctorSquare.base t x₁
    ... | _ | refl
      = FunctorSquare.base s
        (Functor.base J₁ x₁)
  
    map
      : {x₁ y₁ : Category.Object C₁}
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Functor.map (functor-compose' I₂ J₂) (Functor.map F f₁)
        ≅ Functor.map H (Functor.map (functor-compose' I₁ J₁) f₁)
    map {x₁ = x₁} {y₁ = y₁} f₁
      with Functor.base J₂ (Functor.base F x₁)
      | FunctorSquare.base t x₁
      | Functor.base J₂ (Functor.base F y₁)
      | FunctorSquare.base t y₁
      | Functor.map J₂ (Functor.map F f₁)
      | FunctorSquare.map t f₁
    ... | _ | refl | _ | refl | _ | refl
      = FunctorSquare.map s
        (Functor.map J₁ f₁)

  functor-square-compose
    : FunctorSquare G H I₁ I₂
    → FunctorSquare F G J₁ J₂
    → FunctorSquare F H
      (functor-compose' I₁ J₁)
      (functor-compose' I₂ J₂)
  functor-square-compose s t
    = record {FunctorSquareCompose s t}

functor-square-compose'
  : {C₁ C₂ C₃ D₁ D₂ D₃ : Category}
  → {F₁ : Functor C₁ C₂}
  → {F₂ : Functor C₂ C₃}
  → {G₁ : Functor D₁ D₂}
  → {G₂ : Functor D₂ D₃}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → {H₃ : Functor C₃ D₃}
  → FunctorSquare F₂ G₂ H₂ H₃
  → FunctorSquare F₁ G₁ H₁ H₂
  → FunctorSquare
    (functor-compose' F₂ F₁)
    (functor-compose' G₂ G₁) H₁ H₃
functor-square-compose' s₂ s₁
  = functor-square-transpose
    (functor-square-compose
      (functor-square-transpose s₂)
      (functor-square-transpose s₁))

-- ## DependentCategory

record DependentCategory
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
    = Category.compose-eq
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

  map-compose'
    : {x y : Category.Object C}
    → {x' y' z' : Object x}
    → (f : Category.Arrow C x y)
    → (f' : Arrow x y' z')
    → (g' : Arrow x x' y')
    → map f (compose x f' g') ≡ compose y (map f f') (map f g')
  map-compose' f
    = Functor.map-compose
      (functor f)

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

-- ## DependentFunctor

-- ### Definition

record DependentFunctor
  {C D : Category}
  (C' : DependentCategory C)
  (D' : DependentCategory D)
  : Set
  where

  field

    functor
      : Functor C D

  open Functor functor public

  field

    functor'
      : (x : Category.Object C)
      → Functor
        (DependentCategory.category C' x)
        (DependentCategory.category D' (base x))

  base'
    : (x : Category.Object C)
    → (x' : DependentCategory.Object C' x)
    → DependentCategory.Object D' (base x)
  base' x
    = Functor.base
      (functor' x)

  map'
    : (x : Category.Object C)
    → {x' y' : DependentCategory.Object C' x}
    → DependentCategory.Arrow C' x x' y'
    → DependentCategory.Arrow D' (base x) (base' x x') (base' x y')
  map' x
    = Functor.map
      (functor' x)

  map-identity'
    : (x : Category.Object C)
    → (x' : DependentCategory.Object C' x)
    → map' x (DependentCategory.identity C' x x')
      ≡ DependentCategory.identity D' (base x) (base' x x')
  map-identity' x
    = Functor.map-identity
      (functor' x)

  map-compose'
    : (x : Category.Object C)
    → {x' y' z' : DependentCategory.Object C' x}
    → (f : DependentCategory.Arrow C' x y' z')
    → (g : DependentCategory.Arrow C' x x' y')
    → map' x (DependentCategory.compose C' x f g)
      ≡ DependentCategory.compose D' (base x) (map' x f) (map' x g)
  map-compose' x
    = Functor.map-compose
      (functor' x)

  map-compose-eq'
    : (x : Category.Object C)
    → {x' y₁' y₂' z' : DependentCategory.Object C' x}
    → (p : y₁' ≡ y₂')
    → (q : base' x y₁' ≡ base' x y₂')
    → (f : DependentCategory.Arrow C' x y₂' z')
    → (g : DependentCategory.Arrow C' x x' y₁')
    → map' x (DependentCategory.compose-eq C' x p f g)
      ≡ DependentCategory.compose-eq D' (base x) q (map' x f) (map' x g)
  map-compose-eq' x
    = Functor.map-compose-eq
      (functor' x)

  field

    functor-square
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → FunctorSquare
        (DependentCategory.functor C' f)
        (DependentCategory.functor D' (map f))
        (functor' x)
        (functor' y)

  base-commutative
    : {x y : Category.Object C}
    → (f : Category.Arrow C x y)
    → (x' : DependentCategory.Object C' x)
    → base' y (DependentCategory.base C' f x')
      ≅ DependentCategory.base D' (map f) (base' x x')
  base-commutative f
    = FunctorSquare.base
      (functor-square f)

  map-commutative
    : {x y : Category.Object C}
    → {x' y' : DependentCategory.Object C' x}
    → (f : Category.Arrow C x y)
    → (f' : DependentCategory.Arrow C' x x' y')
    → map' y (DependentCategory.map C' f f')
      ≅ DependentCategory.map D' (map f) (map' x f')
  map-commutative f
    = FunctorSquare.map
      (functor-square f)

-- ### Identity

module _
  {C : Category}
  where

  module DependentFunctorIdentity'
    (C' : DependentCategory C)
    where

    functor
      : Functor C C
    functor
      = functor-identity' C

    open Functor functor

    functor'
      : (x : Category.Object C)
      → Functor
        (DependentCategory.category C' x)
        (DependentCategory.category C' (base x))
    functor' x
      = functor-identity'
        (DependentCategory.category C' x)

    abstract

      functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → FunctorSquare
          (DependentCategory.functor C' f)
          (DependentCategory.functor C' (map f))
          (functor' x)
          (functor' y)
      functor-square f
        = functor-square-identity
          (DependentCategory.functor C' f)

  dependent-functor-identity
    : (C' : DependentCategory C)
    → DependentFunctor C' C'
  dependent-functor-identity F
    = record {DependentFunctorIdentity' F}

-- ### Compose

module _
  {C D E : Category}
  {C' : DependentCategory C}
  {D' : DependentCategory D}
  {E' : DependentCategory E}
  where

  module DependentFunctorCompose'
    (F : DependentFunctor D' E')
    (G : DependentFunctor C' D')
    where

    functor
      : Functor C E
    functor
      = functor-compose'
        (DependentFunctor.functor F)
        (DependentFunctor.functor G)

    open Functor functor

    functor'
      : (x : Category.Object C)
      → Functor
        (DependentCategory.category C' x)
        (DependentCategory.category E' (base x))
    functor' x
      = functor-compose'
        (DependentFunctor.functor' F (DependentFunctor.base G x))
        (DependentFunctor.functor' G x)

    abstract

      functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → FunctorSquare
          (DependentCategory.functor C' f)
          (DependentCategory.functor E' (map f))
          (functor' x)
          (functor' y)
      functor-square f
        = functor-square-compose
          (DependentFunctor.functor-square F (DependentFunctor.map G f))
          (DependentFunctor.functor-square G f)

  dependent-functor-compose
    : DependentFunctor D' E'
    → DependentFunctor C' D'
    → DependentFunctor C' E'
  dependent-functor-compose F G
    = record {DependentFunctorCompose' F G}

-- ## DependentFunctorEqual

record DependentFunctorEqual
  {C D : Category}
  {C' : DependentCategory C}
  {D' : DependentCategory D}
  (F₁ F₂ : DependentFunctor C' D')
  : Set
  where

  field

    functor
      : FunctorEqual
        (DependentFunctor.functor F₁)
        (DependentFunctor.functor F₂)

  open FunctorEqual functor public

  field

    functor'
      : (x : Category.Object C)
      → FunctorEqual
        (DependentFunctor.functor' F₁ x)
        (DependentFunctor.functor' F₂ x)

  base'
    : (x : Category.Object C)
    → (x' : DependentCategory.Object C' x)
    → DependentFunctor.base' F₁ x x' ≅ DependentFunctor.base' F₂ x x'
  base' x
    = FunctorEqual.base
      (functor' x)
  
  map'
    : (x : Category.Object C)
    → {x' y' : DependentCategory.Object C' x}
    → (f : DependentCategory.Arrow C' x x' y')
    → DependentFunctor.map' F₁ x f ≅ DependentFunctor.map' F₂ x f
  map' x
    = FunctorEqual.map
      (functor' x)

-- ## DependentFunctorIdentity

-- ### Definition

record DependentFunctorIdentity
  {C : Category}
  {C' : DependentCategory C}
  (F : DependentFunctor C' C')
  : Set
  where

  field

    functor
      : FunctorIdentity
        (DependentFunctor.functor F)
        
  open FunctorIdentity functor public

  field

    functor'
      : (x : Category.Object C)
      → FunctorIdentity
        (DependentFunctor.functor' F x)

  base'
    : (x : Category.Object C)
    → (x' : DependentCategory.Object C' x)
    → DependentFunctor.base' F x x' ≅ x'
  base' x
    = FunctorIdentity.base
      (functor' x)

  map'
    : (x : Category.Object C)
    → {x' y' : DependentCategory.Object C' x}
    → (f : DependentCategory.Arrow C' x x' y')
    → DependentFunctor.map' F x f ≅ f
  map' x
    = FunctorIdentity.map
      (functor' x)

-- ### Conversion

module _
  {C : Category}
  {C' : DependentCategory C}
  {F : DependentFunctor C' C'}
  where

  module DependentFunctorIdentityToEqual
    (p : DependentFunctorIdentity F)
    where

    functor
      : FunctorEqual
        (DependentFunctor.functor F)
        (DependentFunctor.functor (dependent-functor-identity C'))
    functor
      = functor-identity-to-equal
        (DependentFunctorIdentity.functor p)

    functor'
      : (x : Category.Object C)
      → FunctorEqual
        (DependentFunctor.functor' F x)
        (DependentFunctor.functor' (dependent-functor-identity C') x)
    functor' x
      = functor-identity-to-equal
        (DependentFunctorIdentity.functor' p x)

  dependent-functor-identity-to-equal
    : DependentFunctorIdentity F
    → DependentFunctorEqual F (dependent-functor-identity C')
  dependent-functor-identity-to-equal p
    = record {DependentFunctorIdentityToEqual p}

-- ## DependentFunctorCompose

-- ### Definition

record DependentFunctorCompose
  {C D E : Category}
  {C' : DependentCategory C}
  {D' : DependentCategory D}
  {E' : DependentCategory E}
  (F : DependentFunctor D' E')
  (G : DependentFunctor C' D')
  (H : DependentFunctor C' E')
  : Set
  where

  field
    
    functor
      : FunctorCompose
        (DependentFunctor.functor F)
        (DependentFunctor.functor G)
        (DependentFunctor.functor H)

  open FunctorCompose functor public

  field

    functor'
      : (x : Category.Object C)
      → FunctorCompose
        (DependentFunctor.functor' F (DependentFunctor.base G x))
        (DependentFunctor.functor' G x)
        (DependentFunctor.functor' H x)

  base'
    : (x : Category.Object C)
    → (x' : DependentCategory.Object C' x)
    → DependentFunctor.base' H x x'
    ≅ DependentFunctor.base' F
      (DependentFunctor.base G x)
      (DependentFunctor.base' G x x')
  base' x
    = FunctorCompose.base
      (functor' x)

  map'
    : (x : Category.Object C)
    → {x' y' : DependentCategory.Object C' x}
    → (f : DependentCategory.Arrow C' x x' y')
    → DependentFunctor.map' H x f
    ≅ DependentFunctor.map' F
      (DependentFunctor.base G x)
      (DependentFunctor.map' G x f)
  map' x
    = FunctorCompose.map
      (functor' x)

-- ### Conversion

module _
  {C D E : Category}
  {C' : DependentCategory C}
  {D' : DependentCategory D}
  {E' : DependentCategory E}
  {F : DependentFunctor D' E'}
  {G : DependentFunctor C' D'}
  {H : DependentFunctor C' E'}
  where

  module DependentFunctorComposeToEqual
    (p : DependentFunctorCompose F G H)
    where

    functor
      : FunctorEqual
        (DependentFunctor.functor H)
        (DependentFunctor.functor (dependent-functor-compose F G))
    functor
      = functor-compose-to-equal
        (DependentFunctorCompose.functor p)

    functor'
      : (x : Category.Object C)
      → FunctorEqual
        (DependentFunctor.functor' H x)
        (DependentFunctor.functor' (dependent-functor-compose F G) x)
    functor' x
      = functor-compose-to-equal
        (DependentFunctorCompose.functor' p x)

  dependent-functor-compose-to-equal
    : DependentFunctorCompose F G H
    → DependentFunctorEqual H (dependent-functor-compose F G)
  dependent-functor-compose-to-equal p
    = record {DependentFunctorComposeToEqual p}

-- ## DependentFunctorSquare

-- ### Definition

record DependentFunctorSquare
  {C₁ C₂ D₁ D₂ : Category}
  {C₁' : DependentCategory C₁}
  {C₂' : DependentCategory C₂}
  {D₁' : DependentCategory D₁}
  {D₂' : DependentCategory D₂}
  (F : DependentFunctor C₁' C₂')
  (G : DependentFunctor D₁' D₂')
  (H₁ : DependentFunctor C₁' D₁')
  (H₂ : DependentFunctor C₂' D₂')
  : Set
  where

  field
 
    functor
      : FunctorSquare
        (DependentFunctor.functor F)
        (DependentFunctor.functor G)
        (DependentFunctor.functor H₁)
        (DependentFunctor.functor H₂)

  open FunctorSquare functor public

  field

    functor'
      : (x₁ : Category.Object C₁)
      → FunctorSquare
        (DependentFunctor.functor' F x₁)
        (DependentFunctor.functor' G (DependentFunctor.base H₁ x₁))
        (DependentFunctor.functor' H₁ x₁)
        (DependentFunctor.functor' H₂ (DependentFunctor.base F x₁))

  base'
    : (x₁ : Category.Object C₁)
    → (x₁' : DependentCategory.Object C₁' x₁)
    → DependentFunctor.base' H₂
      (DependentFunctor.base F x₁)
      (DependentFunctor.base' F x₁ x₁') 
    ≅ DependentFunctor.base' G
      (DependentFunctor.base H₁ x₁)
      (DependentFunctor.base' H₁ x₁ x₁')
  base' x₁
    = FunctorSquare.base
      (functor' x₁)

  map'
    : (x₁ : Category.Object C₁)
    → {x₁' y₁' : DependentCategory.Object C₁' x₁}
    → (f₁ : DependentCategory.Arrow C₁' x₁ x₁' y₁')
    → DependentFunctor.map' H₂
      (DependentFunctor.base F x₁)
      (DependentFunctor.map' F x₁ f₁)
    ≅ DependentFunctor.map' G
      (DependentFunctor.base H₁ x₁)
      (DependentFunctor.map' H₁ x₁ f₁)
  map' x₁
    = FunctorSquare.map
      (functor' x₁)

-- ### Conversion

module _
  {C₁ C₂ D₁ D₂ : Category}
  {C₁' : DependentCategory C₁}
  {C₂' : DependentCategory C₂}
  {D₁' : DependentCategory D₁}
  {D₂' : DependentCategory D₂}
  {F : DependentFunctor C₁' C₂'}
  {G : DependentFunctor D₁' D₂'}
  {H₁ : DependentFunctor C₁' D₁'}
  {H₂ : DependentFunctor C₂' D₂'}
  where

  module DependentFunctorSquareToEqual
    (s : DependentFunctorSquare F G H₁ H₂)
    where

    functor
      : FunctorEqual
        (DependentFunctor.functor (dependent-functor-compose H₂ F))
        (DependentFunctor.functor (dependent-functor-compose G H₁))
    functor
      = functor-square-to-equal
        (DependentFunctorSquare.functor s)

    functor'
      : (x₁ : Category.Object C₁)
      → FunctorEqual
        (DependentFunctor.functor' (dependent-functor-compose H₂ F) x₁)
        (DependentFunctor.functor' (dependent-functor-compose G H₁) x₁)
    functor' x₁
      = functor-square-to-equal
        (DependentFunctorSquare.functor' s x₁)

  dependent-functor-square-to-equal
    : DependentFunctorSquare F G H₁ H₂
    → DependentFunctorEqual
      (dependent-functor-compose H₂ F)
      (dependent-functor-compose G H₁)
  dependent-functor-square-to-equal s
    = record {DependentFunctorSquareToEqual s}

