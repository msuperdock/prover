module Prover.Category where

open import Prover.Function
  using (Function; FunctionCompose; FunctionEqual; FunctionIdentity;
    FunctionSquare)
open import Prover.Prelude

-- ## Precategory

record Precategory
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

    ArrowEqual
      : {x y : Object}
      → Arrow x y
      → Arrow x y
      → Set

    arrow-refl
      : {x y : Object}
      → {f : Arrow x y}
      → ArrowEqual f f

    arrow-sym
      : {x y : Object}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁

    arrow-trans
      : {x y : Object}
      → {f₁ f₂ f₃ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃

    identity
      : (x : Object)
      → Arrow x x

    compose
      : {x y z : Object}
      → Arrow y z
      → Arrow x y
      → Arrow x z

-- ## Category

-- ### Definition

record Category''
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

    ArrowEqual
      : {x y : Object}
      → Arrow x y
      → Arrow x y
      → Set

    arrow-refl
      : {x y : Object}
      → {f : Arrow x y}
      → ArrowEqual f f

    arrow-sym
      : {x y : Object}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁

    arrow-trans
      : {x y : Object}
      → {f₁ f₂ f₃ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃

    simplify
      : {x y : Object}
      → Arrow x y
      → Arrow x y

    simplify-equal
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (simplify f) f

    identity
      : (x : Object)
      → Arrow x x

    compose
      : {x y z : Object}
      → Arrow y z
      → Arrow x y
      → Arrow x z

    compose-equal
      : {x y z : Object}
      → {f₁ f₂ : Arrow y z}
      → {g₁ g₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual g₁ g₂
      → ArrowEqual
        (compose f₁ g₁)
        (compose f₂ g₂)

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (compose f (identity x)) f

    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → ArrowEqual
        (compose (identity y) f) f

    associative
      : {w x y z : Object}
      → (f : Arrow y z)
      → (g : Arrow x y)
      → (h : Arrow w x)
      → ArrowEqual
        (compose (compose f g) h)
        (compose f (compose g h))

Category
  = Category''

-- ### Equality

data ArrowEqual''
  : (C₁ C₂ : Category'')
  → {x₁ y₁ : Category''.Object C₁}
  → {x₂ y₂ : Category''.Object C₂}
  → Category''.Arrow C₁ x₁ y₁
  → Category''.Arrow C₂ x₂ y₂
  → Set
  where

  any
    : {C : Category''}
    → {x y : Category''.Object C}
    → {f₁ f₂ : Category''.Arrow C x y}
    → Category''.ArrowEqual C f₁ f₂
    → ArrowEqual'' C C f₁ f₂

-- ### Module

module Category
  (C : Category)
  where

  open Category'' C public

  open ArrowEqual'' public
    using (any)

  ArrowEqual'
    : {x₁ y₁ : Object}
    → {x₂ y₂ : Object}
    → Arrow x₁ y₁
    → Arrow x₂ y₂
    → Set
  ArrowEqual'
    = ArrowEqual'' C C

  any'
    : {x y : Object}
    → {f₁ f₂ : Arrow x y}
    → ArrowEqual' f₁ f₂
    → ArrowEqual f₁ f₂
  any' (any p)
    = p

  arrow-refl'
    : {x y : Object}
    → {f : Arrow x y}
    → ArrowEqual' f f
  arrow-refl'
    = any arrow-refl

  arrow-sym'
    : {x₁ x₂ y₁ y₂ : Object}
    → {f₁ : Arrow x₁ y₁}
    → {f₂ : Arrow x₂ y₂}
    → ArrowEqual' f₁ f₂
    → ArrowEqual' f₂ f₁
  arrow-sym' (any p)
    = any (arrow-sym p)

  arrow-trans'
    : {x₁ x₂ x₃ y₁ y₂ y₃ : Object}
    → {f₁ : Arrow x₁ y₁}
    → {f₂ : Arrow x₂ y₂}
    → {f₃ : Arrow x₃ y₃}
    → ArrowEqual' f₁ f₂
    → ArrowEqual' f₂ f₃
    → ArrowEqual' f₁ f₃
  arrow-trans' (any p₁) (any p₂)
    = any (arrow-trans p₁ p₂)

  simplify-equal'
    : {x y : Object}
    → (f : Arrow x y)
    → ArrowEqual'
      (simplify f) f
  simplify-equal' f
    = any (simplify-equal f)

  identity-equal
    : {x₁ x₂ : Object}
    → x₁ ≡ x₂
    → ArrowEqual'
      (identity x₁)
      (identity x₂)
  identity-equal refl
    = arrow-refl'

  compose'
    : {x y₁ y₂ z : Object}
    → y₁ ≡ y₂
    → Arrow y₂ z
    → Arrow x y₁
    → Arrow x z
  compose' refl
    = compose

  compose-equal'
    : {x₁ x₂ y₁ y₂ z₁ z₂ : Object}
    → {f₁ : Arrow y₁ z₁}
    → {f₂ : Arrow y₂ z₂}
    → {g₁ : Arrow x₁ y₁}
    → {g₂ : Arrow x₂ y₂}
    → ArrowEqual' f₁ f₂
    → ArrowEqual' g₁ g₂
    → ArrowEqual'
      (compose f₁ g₁)
      (compose f₂ g₂)
  compose-equal' (any p) (any q)
    = any (compose-equal p q)

  compose-equal''
    : {x₁ x₂ y₁ y₂ z : Object}
    → (p : y₁ ≡ y₂)
    → (f : Arrow y₂ z)
    → {g₁ : Arrow x₁ y₁}
    → {g₂ : Arrow x₂ y₂}
    → ArrowEqual' g₁ g₂
    → ArrowEqual'
      (compose' p f g₁)
      (compose f g₂)
  compose-equal'' refl _
    = compose-equal' arrow-refl'

  precompose'
    : {x y : Object}
    → (f : Arrow x y)
    → ArrowEqual'
      (compose f (identity x)) f
  precompose' f
    = any (precompose f)

  postcompose'
    : {x y : Object}
    → (f : Arrow x y)
    → ArrowEqual'
      (compose (identity y) f) f
  postcompose' f
    = any (postcompose f)

  associative'
    : {w x y z : Object}
    → (f : Arrow y z)
    → (g : Arrow x y)
    → (h : Arrow w x)
    → ArrowEqual'
      (compose (compose f g) h)
      (compose f (compose g h))
  associative' f g h
    = any (associative f g h)

  arrow
    : {x₁ x₂ y₁ y₂ : Object}
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → Arrow x₂ y₂
    → Arrow x₁ y₁
  arrow refl refl
    = id

  arrow-equal
    : {x₁ x₂ y₁ y₂ : Object}
    → {f₁ f₂ : Arrow x₂ y₂}
    → (p : x₁ ≡ x₂)
    → (q : y₁ ≡ y₂)
    → ArrowEqual f₁ f₂
    → ArrowEqual
      (arrow p q f₁)
      (arrow p q f₂)
  arrow-equal refl refl
    = id

  arrow-equal'
    : {x₁ x₂ y₁ y₂ : Object}
    → (p : x₁ ≡ x₂)
    → (q : y₁ ≡ y₂)
    → (f : Arrow x₂ y₂)
    → ArrowEqual'
      (arrow p q f) f
  arrow-equal' refl refl _
    = arrow-refl'

  arrow-compose
    : {x₁ x₂ y₁ y₂ z₁ z₂ : Object}
    → (p : x₁ ≡ x₂)
    → (q : y₁ ≡ y₂)
    → (r : z₁ ≡ z₂)
    → (f : Arrow y₂ z₂)
    → (g : Arrow x₂ y₂)
    → ArrowEqual
      (arrow p r (compose f g))
      (compose (arrow q r f) (arrow p q g))
  arrow-compose refl refl refl _ _
    = arrow-refl

-- ### Module'

module Category' where

  ArrowEqual'
    = ArrowEqual''

  arrow-trans'
    : {C₁ C₂ C₃ : Category}
    → {x₁ y₁ : Category.Object C₁}
    → {x₂ y₂ : Category.Object C₂}
    → {x₃ y₃ : Category.Object C₃}
    → {f₁ : Category.Arrow C₁ x₁ y₁}
    → {f₂ : Category.Arrow C₂ x₂ y₂}
    → {f₃ : Category.Arrow C₃ x₃ y₃}
    → ArrowEqual' C₁ C₂ f₁ f₂
    → ArrowEqual' C₂ C₃ f₂ f₃
    → ArrowEqual' C₁ C₃ f₁ f₃
  arrow-trans' {C₁ = C₁} p₁@(any _) p₂@(any _)
    = Category.arrow-trans' C₁ p₁ p₂

-- ## Prefunctor

record Prefunctor
  (C : Precategory)
  (D : Category)
  : Set
  where

  no-eta-equality

  field

    base
      : Precategory.Object C
      → Category.Object D

    map
      : {x y : Precategory.Object C}
      → Precategory.Arrow C x y
      → Category.Arrow D (base x) (base y)

    map-equal
      : {x y : Precategory.Object C}
      → {f₁ f₂ : Precategory.Arrow C x y}
      → Precategory.ArrowEqual C f₁ f₂
      → Category.ArrowEqual D (map f₁) (map f₂)

    map-identity
      : (x : Precategory.Object C)
      → Category.ArrowEqual D
        (map (Precategory.identity C x))
        (Category.identity D (base x))

    map-compose
      : {x y z : Precategory.Object C}
      → (f : Precategory.Arrow C y z)
      → (g : Precategory.Arrow C x y)
      → Category.ArrowEqual D
        (map (Precategory.compose C f g))
        (Category.compose D (map f) (map g))

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

  function
    : Function
      (Category.Object C)
      (Category.Object D)
  function
    = record
    { base
      = base
    }

  field

    map
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → Category.Arrow D (base x) (base y)

    map-equal
      : {x y : Category.Object C}
      → {f₁ f₂ : Category.Arrow C x y}
      → Category.ArrowEqual C f₁ f₂
      → Category.ArrowEqual D (map f₁) (map f₂)

    map-identity
      : (x : Category.Object C)
      → Category.ArrowEqual D
        (map (Category.identity C x))
        (Category.identity D (base x))

    map-compose
      : {x y z : Category.Object C}
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → Category.ArrowEqual D
        (map (Category.compose C f g))
        (Category.compose D (map f) (map g))

  map-equal'
    : {x₁ x₂ y₁ y₂ : Category.Object C}
    → {f₁ : Category.Arrow C x₁ y₁}
    → {f₂ : Category.Arrow C x₂ y₂}
    → Category.ArrowEqual' C f₁ f₂
    → Category.ArrowEqual' D (map f₁) (map f₂)
  map-equal' (any p)
    = any (map-equal p)

  map-identity'
    : (x : Category.Object C)
    → Category.ArrowEqual' D
      (map (Category.identity C x))
      (Category.identity D (base x))
  map-identity' x
    = any (map-identity x)

  map-compose'
    : {x y z : Category.Object C}
    → (f : Category.Arrow C y z)
    → (g : Category.Arrow C x y)
    → Category.ArrowEqual' D
      (map (Category.compose C f g))
      (Category.compose D (map f) (map g))
  map-compose' f g
    = any (map-compose f g)

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

    map-equal
      : {x y : Category.Object C}
      → {f₁ f₂ : Category.Arrow C x y}
      → Category.ArrowEqual C f₁ f₂
      → Category.ArrowEqual C (map f₁) (map f₂)
    map-equal
      = id

    map-identity
      : (x : Category.Object C)
      → Category.ArrowEqual C
        (map (Category.identity C x))
        (Category.identity C (base x))
    map-identity _
      = Category.arrow-refl C
  
    map-compose
      : {x y z : Category.Object C}
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → Category.ArrowEqual C
        (map (Category.compose C f g))
        (Category.compose C (map f) (map g))
    map-compose _ _
      = Category.arrow-refl C

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

      map-equal
        : {x y : Category.Object C}
        → {f₁ f₂ : Category.Arrow C x y}
        → Category.ArrowEqual C f₁ f₂
        → Category.ArrowEqual E (map f₁) (map f₂)
      map-equal
        = Functor.map-equal F
        ∘ Functor.map-equal G

      map-identity
        : (x : Category.Object C)
        → Category.ArrowEqual E
          (map (Category.identity C x))
          (Category.identity E (base x))
      map-identity x
        = Category.arrow-trans E (Functor.map-equal F
          (Functor.map-identity G x))
        $ Functor.map-identity F (Functor.base G x)
  
      map-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → Category.ArrowEqual E
          (map (Category.compose C f g))
          (Category.compose E (map f) (map g))
      map-compose f g
        = Category.arrow-trans E (Functor.map-equal F
          (Functor.map-compose G f g))
        $ Functor.map-compose F (Functor.map G f) (Functor.map G g)

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
  
  function
    : FunctionEqual
      (Functor.function F₁)
      (Functor.function F₂)
  function
    = record
    { base
      = base
    }

  field

    map
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → Category'.ArrowEqual' D₁ D₂
        (Functor.map F₁ f)
        (Functor.map F₂ f)

  map'
    : {x₁ x₂ y₁ y₂ : Category.Object C}
    → {f₁ : Category.Arrow C x₁ y₁}
    → {f₂ : Category.Arrow C x₂ y₂}
    → Category.ArrowEqual' C f₁ f₂
    → Category'.ArrowEqual' D₁ D₂
      (Functor.map F₁ f₁)
      (Functor.map F₂ f₂)
  map' {f₁ = f₁} p
    = Category'.arrow-trans' (map f₁)
    $ Functor.map-equal' F₂ p

-- ### Symmetry

functor-sym
  : {C D : Category}
  → {F₁ F₂ : Functor C D}
  → FunctorEqual F₁ F₂
  → FunctorEqual F₂ F₁
functor-sym {D = D} p
  = record
  { base
    = λ x → sym
      (FunctorEqual.base p x)
  ; map
    = λ f → Category.arrow-sym' D
      (FunctorEqual.map p f)
  }

-- ### Transitivity
  
functor-trans
  : {C D : Category}
  → {F₁ F₂ F₃ : Functor C D}
  → FunctorEqual F₁ F₂
  → FunctorEqual F₂ F₃
  → FunctorEqual F₁ F₃
functor-trans {D = D} p₁ p₂
  = record
  { base
    = λ x → trans
      (FunctorEqual.base p₁ x)
      (FunctorEqual.base p₂ x)
  ; map
    = λ f → Category.arrow-trans' D
      (FunctorEqual.map p₁ f)
      (FunctorEqual.map p₂ f)
  }

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

  function
    : FunctionIdentity
      (Functor.function F)
  function
    = record
    { base
      = base
    }

  field

    map
      : {x₁ y₁ : Category.Object C₁}
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Category'.ArrowEqual' C₂ C₁
        (Functor.map F f₁) f₁

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

  function
    : FunctionCompose
      (Functor.function F)
      (Functor.function G)
      (Functor.function H)
  function
    = record
    { base
      = base
    }

  field

    map
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → Category'.ArrowEqual' E₂ E₁
        (Functor.map H f)
        (Functor.map F (Functor.map G f))

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

  function
    : FunctionSquare
      (Functor.function F)
      (Functor.function G)
      (Functor.function H₁)
      (Functor.function H₂)
  function
    = record
    { base
      = base
    }

  field
  
    map
      : {x₁ y₁ : Category.Object C₁}
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Category'.ArrowEqual' D₂ D₃
        (Functor.map H₂ (Functor.map F f₁))
        (Functor.map G (Functor.map H₁ f₁))

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

functor-square-transpose
  : {C₁ C₂ D₁ D₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → FunctorSquare F G H₁ H₂
  → FunctorSquare H₁ H₂ F G
functor-square-transpose {D₂ = D₂} s
  = record
  { base
    = λ x₁ → sym
      (FunctorSquare.base s x₁)
  ; map
    = λ f₁ → Category.arrow-sym' D₂
      (FunctorSquare.map s f₁)
  }

-- ### Identity

functor-square-identity
  : {C₁ C₂ : Category}
  → (F : Functor C₁ C₂)
  → FunctorSquare F F
    (functor-identity' C₁)
    (functor-identity' C₂)
functor-square-identity {C₂ = C₂} _
  = record
  { base
    = λ _ → refl
  ; map
    = λ _ → Category.arrow-refl' C₂
  }

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

functor-square-compose
  : {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H : Functor E₁ E₂}
  → {I₁ : Functor D₁ E₁}
  → {I₂ : Functor D₂ E₂}
  → {J₁ : Functor C₁ D₁}
  → {J₂ : Functor C₂ D₂}
  → FunctorSquare G H I₁ I₂
  → FunctorSquare F G J₁ J₂
  → FunctorSquare F H
    (functor-compose' I₁ J₁)
    (functor-compose' I₂ J₂)
functor-square-compose {E₂ = E₂} {I₂ = I₂} {J₁ = J₁} s t
  = record
  { base
    = λ x₁
    → trans (sub (Functor.base I₂) (FunctorSquare.base t x₁))
    $ FunctorSquare.base s (Functor.base J₁ x₁)
  ; map
    = λ f₁
    → Category.arrow-trans' E₂ (Functor.map-equal' I₂ (FunctorSquare.map t f₁))
    $ FunctorSquare.map s (Functor.map J₁ f₁)
  }

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

