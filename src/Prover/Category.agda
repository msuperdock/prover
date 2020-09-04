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
    → (f : Arrow x₂ y₂)
    → arrow p q f ≅ f
  arrow-eq refl refl _
    = refl

  identity-eq
    : {x₁ x₂ : Object}
    → x₁ ≡ x₂
    → identity x₁ ≅ identity x₂
  identity-eq refl
    = refl

  compose-eq
    : {x₁ x₂ y₁ y₂ z₁ z₂ : Object}
    → {f₁ : Arrow y₁ z₁}
    → {f₂ : Arrow y₂ z₂}
    → {g₁ : Arrow x₁ y₁}
    → {g₂ : Arrow x₂ y₂}
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → z₁ ≡ z₂
    → f₁ ≅ f₂
    → g₁ ≅ g₂
    → compose f₁ g₁ ≅ compose f₂ g₂
  compose-eq refl refl refl refl refl
    = refl

  compose-eq'
    : {x y₁ y₂ z : Object}
    → y₁ ≡ y₂
    → Arrow y₂ z
    → Arrow x y₁
    → Arrow x z
  compose-eq' refl
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

  map-eq
    : {x₁ x₂ y₁ y₂ : Category.Object C}
    → {f₁ : Category.Arrow C x₁ y₁}
    → {f₂ : Category.Arrow C x₂ y₂}
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → f₁ ≅ f₂
    → map f₁ ≅ map f₂
  map-eq refl refl refl
    = refl

  map-compose-eq
    : {x y₁ y₂ z : Category.Object C}
    → (p : y₁ ≡ y₂)
    → (q : base y₁ ≡ base y₂)
    → (f : Category.Arrow C y₂ z)
    → (g : Category.Arrow C x y₁)
    → map (Category.compose-eq' C p f g)
      ≡ Category.compose-eq' D q (map f) (map g)
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

-- ### Equality

module _
  {C₁ C₂ : Category}
  where

  functor-identity-to-equal
    : {F : Functor C₁ C₂}
    → FunctorIdentity F
    → FunctorEqual F (functor-identity' C₁)
  functor-identity-to-equal p
    = record {FunctorIdentity p}
  
  functor-identity-from-equal
    : {F : Functor C₁ C₂}
    → FunctorEqual F (functor-identity' C₁)
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

-- ### Equality

module _
  {C D E₁ E₂ : Category}
  where

  functor-compose-to-equal
    : {F : Functor D E₁}
    → {G : Functor C D}
    → {H : Functor C E₂}
    → FunctorCompose F G H
    → FunctorEqual H (functor-compose' F G)
  functor-compose-to-equal p
    = record {FunctorCompose p}
  
  functor-compose-from-equal
    : (F : Functor D E₁)
    → (G : Functor C D)
    → {H : Functor C E₂}
    → FunctorEqual H (functor-compose' F G)
    → FunctorCompose F G H
  functor-compose-from-equal _ _ p
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

-- ### Equality

module _
  {C₁ C₂ D₁ D₂ D₃ : Category}
  where

  functor-square-to-equal
    : {F : Functor C₁ C₂}
    → {G : Functor D₁ D₃}
    → {H₁ : Functor C₁ D₁}
    → {H₂ : Functor C₂ D₂}
    → FunctorSquare F G H₁ H₂
    → FunctorEqual (functor-compose' H₂ F) (functor-compose' G H₁)
  functor-square-to-equal s
    = record {FunctorSquare s}
  
  functor-square-from-equal
    : (F : Functor C₁ C₂)
    → (G : Functor D₁ D₃)
    → (H₁ : Functor C₁ D₁)
    → (H₂ : Functor C₂ D₂)
    → FunctorEqual (functor-compose' H₂ F) (functor-compose' G H₁)
    → FunctorSquare F G H₁ H₂
  functor-square-from-equal _ _ _ _ p
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

