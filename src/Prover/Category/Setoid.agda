module Prover.Category.Setoid where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Prelude

-- ## SetoidCategory

-- ### Definition

record SetoidCategory
  : Set₁
  where

  no-eta-equality

  field

    Object
      : Set

    ArrowSetoid
      : Object
      → Object
      → Setoid

  Arrow
    : Object
    → Object
    → Set
  Arrow x y
    = Setoid.Element
      (ArrowSetoid x y)

  ArrowEqual
    : {x y : Object}
    → Arrow x y
    → Arrow x y
    → Set
  ArrowEqual {x} {y}
    = Setoid.ElementEqual
      (ArrowSetoid x y)

  arrow-refl
    : {x y : Object}
    → {f : Arrow x y}
    → ArrowEqual f f
  arrow-refl {x} {y}
    = Setoid.element-refl
      (ArrowSetoid x y)

  arrow-sym
    : {x y : Object}
    → {f₁ f₂ : Arrow x y}
    → ArrowEqual f₁ f₂
    → ArrowEqual f₂ f₁
  arrow-sym {x} {y}
    = Setoid.element-sym
      (ArrowSetoid x y)

  arrow-trans
    : {x y : Object}
    → {f₁ f₂ f₃ : Arrow x y}
    → ArrowEqual f₁ f₂
    → ArrowEqual f₂ f₃
    → ArrowEqual f₁ f₃
  arrow-trans {x} {y}
    = Setoid.element-trans
      (ArrowSetoid x y)

  field

    identity
      : (x : Object)
      → Arrow x x

    compose
      : {x y z : Object}
      → Arrow y z
      → Arrow x y
      → Arrow x z

    compose-eq
      : {x y z : Object}
      → {f₁ f₂ : Arrow y z}
      → {g₁ g₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual g₁ g₂
      → ArrowEqual
        (compose f₁ g₁)
        (compose f₂ g₂)

  compose-eq₁
    : {x y z : Object}
    → {f₁ f₂ : Arrow y z}
    → (g : Arrow x y)
    → ArrowEqual f₁ f₂
    → ArrowEqual
      (compose f₁ g)
      (compose f₂ g)
  compose-eq₁ _ p
    = compose-eq p arrow-refl

  compose-eq₂
    : {x y z : Object}
    → {g₁ g₂ : Arrow x y}
    → (f : Arrow y z)
    → ArrowEqual g₁ g₂
    → ArrowEqual
      (compose f g₁)
      (compose f g₂)
  compose-eq₂ _ p
    = compose-eq arrow-refl p

  field

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

  data ArrowEqual'
    : {x₁ x₂ y₁ y₂ : Object}
    → Arrow x₁ y₁
    → Arrow x₂ y₂
    → Set
    where

    arrow-equal'
      : {x y : Object}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual' f₁ f₂

  arrow-sym'
    : {x₁ x₂ y₁ y₂ : Object}
    → {f₁ : Arrow x₁ y₁}
    → {f₂ : Arrow x₂ y₂}
    → ArrowEqual' f₁ f₂
    → ArrowEqual' f₂ f₁
  arrow-sym' (arrow-equal' p)
    = arrow-equal' (arrow-sym p)

  arrow-trans'
    : {x₁ x₂ x₃ y₁ y₂ y₃ : Object}
    → {f₁ : Arrow x₁ y₁}
    → {f₂ : Arrow x₂ y₂}
    → {f₃ : Arrow x₃ y₃}
    → ArrowEqual' f₁ f₂
    → ArrowEqual' f₂ f₃
    → ArrowEqual' f₁ f₃
  arrow-trans' (arrow-equal' p₁) (arrow-equal' p₂)
    = arrow-equal' (arrow-trans p₁ p₂)

-- ### Conversion

module CategorySetoid
  (C : SetoidCategory)
  (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
  (I : (x y : SetoidCategory.Object C)
    → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
  where

  to
    : {x y : SetoidCategory.Object C}
    → C' x y
    → SetoidCategory.Arrow C x y
  to {x = x} {y = y}
    = SetoidIsomorphism.to (I x y)

  from
    : {x y : SetoidCategory.Object C}
    → SetoidCategory.Arrow C x y
    → C' x y
  from {x = x} {y = y}
    = SetoidIsomorphism.from (I x y)

  from-eq
    : {x y : SetoidCategory.Object C}
    → {f₁ f₂ : SetoidCategory.Arrow C x y}
    → SetoidCategory.ArrowEqual C f₁ f₂
    → from f₁ ≡ from f₂
  from-eq {x = x} {y = y}
    = SetoidIsomorphism.from-eq (I x y)

  from-eq'
    : {x₁ x₂ y₁ y₂ : SetoidCategory.Object C}
    → {f₁ : SetoidCategory.Arrow C x₁ y₁}
    → {f₂ : SetoidCategory.Arrow C x₂ y₂}
    → SetoidCategory.ArrowEqual' C f₁ f₂
    → from f₁ ≅ from f₂
  from-eq' (SetoidCategory.arrow-equal' p)
    = from-eq p

  from-to
    : {x y : SetoidCategory.Object C}
    → (f : C' x y)
    → from (to f) ≡ f
  from-to {x = x} {y = y}
    = SetoidIsomorphism.from-to (I x y)

  to-from
    : {x y : SetoidCategory.Object C}
    → (f : SetoidCategory.Arrow C x y)
    → SetoidCategory.ArrowEqual C (to (from f)) f
  to-from {x = x} {y = y}
    = SetoidIsomorphism.to-from (I x y)

  Object
    : Set
  Object
    = SetoidCategory.Object C

  Arrow
    : Object
    → Object
    → Set
  Arrow
    = C'

  identity
    : (x : Object)
    → Arrow x x
  identity x
    = from (SetoidCategory.identity C x)

  compose
    : {x y z : Object}
    → Arrow y z
    → Arrow x y
    → Arrow x z
  compose f g
    = from (SetoidCategory.compose C (to f) (to g))

  abstract

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose f (identity x) ≡ f
    precompose {x = x} f
      = trans (from-eq (SetoidCategory.compose-eq₂ C (to f)
        (to-from (SetoidCategory.identity C x))))
      $ trans (from-eq (SetoidCategory.precompose C (to f)))
      $ from-to f

    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose (identity y) f ≡ f
    postcompose {y = y} f
      = trans (from-eq (SetoidCategory.compose-eq₁ C (to f)
        (to-from (SetoidCategory.identity C y))))
      $ trans (from-eq (SetoidCategory.postcompose C (to f)))
      $ from-to f

    associative
      : {w x y z : Object}
      → (f : Arrow y z)
      → (g : Arrow x y)
      → (h : Arrow w x)
      → compose (compose f g) h ≡ compose f (compose g h)
    associative f g h
      = trans (from-eq (SetoidCategory.compose-eq₁ C (to h)
        (to-from (SetoidCategory.compose C (to f) (to g)))))
      $ trans (from-eq (SetoidCategory.associative C (to f) (to g) (to h)))
      $ sym (from-eq (SetoidCategory.compose-eq₂ C (to f)
        (to-from (SetoidCategory.compose C (to g) (to h)))))

category-setoid
  : (C : SetoidCategory)
  → (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
  → ((x y : SetoidCategory.Object C)
    → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
  → Category
category-setoid C C' I
  = record {CategorySetoid C C' I}

-- ## SetoidFunctor

-- ### Definition

record SetoidFunctor
  (C D : SetoidCategory)
  : Set
  where

  no-eta-equality

  field

    base
      : SetoidCategory.Object C
      → SetoidCategory.Object D

    map
      : {x y : SetoidCategory.Object C}
      → SetoidCategory.Arrow C x y
      → SetoidCategory.Arrow D (base x) (base y)

    map-eq
      : {x y : SetoidCategory.Object C}
      → {f₁ f₂ : SetoidCategory.Arrow C x y}
      → SetoidCategory.ArrowEqual C f₁ f₂
      → SetoidCategory.ArrowEqual D (map f₁) (map f₂)

    map-identity
      : (x : SetoidCategory.Object C)
      → SetoidCategory.ArrowEqual D
        (map (SetoidCategory.identity C x))
        (SetoidCategory.identity D (base x))

    map-compose
      : {x y z : SetoidCategory.Object C}
      → (f : SetoidCategory.Arrow C y z)
      → (g : SetoidCategory.Arrow C x y)
      → SetoidCategory.ArrowEqual D
        (map (SetoidCategory.compose C f g))
        (SetoidCategory.compose D (map f) (map g))

-- ### Identity

module SetoidFunctorIdentity'
  (C : SetoidCategory)
  where

  base
    : SetoidCategory.Object C
    → SetoidCategory.Object C
  base
    = id

  map
    : {x y : SetoidCategory.Object C}
    → SetoidCategory.Arrow C x y
    → SetoidCategory.Arrow C (base x) (base y)
  map
    = id

  abstract

    map-eq
      : {x y : SetoidCategory.Object C}
      → {f₁ f₂ : SetoidCategory.Arrow C x y}
      → SetoidCategory.ArrowEqual C f₁ f₂
      → SetoidCategory.ArrowEqual C (map f₁) (map f₂)
    map-eq
      = id

    map-identity
      : (x : SetoidCategory.Object C)
      → SetoidCategory.ArrowEqual C
        (map (SetoidCategory.identity C x))
        (SetoidCategory.identity C (base x))
    map-identity _
      = SetoidCategory.arrow-refl C

    map-compose
      : {x y z : SetoidCategory.Object C}
      → (f : SetoidCategory.Arrow C y z)
      → (g : SetoidCategory.Arrow C x y)
      → SetoidCategory.ArrowEqual C
        (map (SetoidCategory.compose C f g))
        (SetoidCategory.compose C (map f) (map g))
    map-compose _ _
      = SetoidCategory.arrow-refl C

setoid-functor-identity
  : (C : SetoidCategory)
  → SetoidFunctor C C
setoid-functor-identity C
  = record {SetoidFunctorIdentity' C}

-- ### Compose

module _
  {C D E : SetoidCategory}
  where

  module SetoidFunctorCompose'
    (F : SetoidFunctor D E)
    (G : SetoidFunctor C D)
    where

    base
      : SetoidCategory.Object C
      → SetoidCategory.Object E
    base
      = SetoidFunctor.base F
      ∘ SetoidFunctor.base G

    map
      : {x y : SetoidCategory.Object C}
      → SetoidCategory.Arrow C x y
      → SetoidCategory.Arrow E (base x) (base y)
    map
      = SetoidFunctor.map F
      ∘ SetoidFunctor.map G

    abstract

      map-eq
        : {x y : SetoidCategory.Object C}
        → {f₁ f₂ : SetoidCategory.Arrow C x y}
        → SetoidCategory.ArrowEqual C f₁ f₂
        → SetoidCategory.ArrowEqual E (map f₁) (map f₂)
      map-eq
        = SetoidFunctor.map-eq F
        ∘ SetoidFunctor.map-eq G

      map-identity
        : (x : SetoidCategory.Object C)
        → SetoidCategory.ArrowEqual E
          (map (SetoidCategory.identity C x))
          (SetoidCategory.identity E (base x))
      map-identity x
        = SetoidCategory.arrow-trans E
          (SetoidFunctor.map-eq F
            (SetoidFunctor.map-identity G x))
          (SetoidFunctor.map-identity F
            (SetoidFunctor.base G x))

      map-compose
        : {x y z : SetoidCategory.Object C}
        → (f : SetoidCategory.Arrow C y z)
        → (g : SetoidCategory.Arrow C x y)
        → SetoidCategory.ArrowEqual E
          (map (SetoidCategory.compose C f g))
          (SetoidCategory.compose E (map f) (map g))
      map-compose f g
        = SetoidCategory.arrow-trans E
          (SetoidFunctor.map-eq F
            (SetoidFunctor.map-compose G f g))
          (SetoidFunctor.map-compose F
            (SetoidFunctor.map G f)
            (SetoidFunctor.map G g))

  setoid-functor-compose
    : SetoidFunctor D E
    → SetoidFunctor C D
    → SetoidFunctor C E
  setoid-functor-compose F G
    = record {SetoidFunctorCompose' F G}

-- ### Conversion

module _
  {C D : SetoidCategory}
  where

  module FunctorSetoid
    (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    (D' : SetoidCategory.Object D → SetoidCategory.Object D → Set)
    (I : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    (J : (x y : SetoidCategory.Object D)
      → SetoidIsomorphism (D' x y) (SetoidCategory.ArrowSetoid D x y))
    (F : SetoidFunctor C D)
    where

    open CategorySetoid
      using (from; from-eq; to; to-from)

    base
      : Category.Object (category-setoid C C' I)
      → Category.Object (category-setoid D D' J)
    base
      = SetoidFunctor.base F

    map
      : {x y : Category.Object (category-setoid C C' I)}
      → Category.Arrow (category-setoid C C' I) x y
      → Category.Arrow (category-setoid D D' J) (base x) (base y)
    map
      = from D D' J
      ∘ SetoidFunctor.map F
      ∘ to C C' I

    abstract

      map-identity
        : (x : Category.Object (category-setoid C C' I))
        → map (Category.identity (category-setoid C C' I) x)
          ≡ Category.identity (category-setoid D D' J) (base x)
      map-identity x
        = trans (from-eq D D' J (SetoidFunctor.map-eq F
          (to-from C C' I (SetoidCategory.identity C x))))
        $ from-eq D D' J (SetoidFunctor.map-identity F x)

      map-compose
        : {x y z : Category.Object (category-setoid C C' I)}
        → (f : Category.Arrow (category-setoid C C' I) y z)
        → (g : Category.Arrow (category-setoid C C' I) x y)
        → map (Category.compose (category-setoid C C' I) f g)
          ≡ Category.compose (category-setoid D D' J) (map f) (map g)
      map-compose f g
        = trans (from-eq D D' J (SetoidFunctor.map-eq F
          (to-from C C' I (SetoidCategory.compose C (to C C' I f) (to C C' I g)))))
        $ trans (from-eq D D' J (SetoidFunctor.map-compose F
          (to C C' I f) (to C C' I g)))
        $ sym (from-eq D D' J (SetoidCategory.compose-eq D
          (to-from D D' J (SetoidFunctor.map F (to C C' I f)))
          (to-from D D' J (SetoidFunctor.map F (to C C' I g)))))

  functor-setoid
    : (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    → (D' : SetoidCategory.Object D → SetoidCategory.Object D → Set)
    → (I : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    → (J : (x y : SetoidCategory.Object D)
      → SetoidIsomorphism (D' x y) (SetoidCategory.ArrowSetoid D x y))
    → SetoidFunctor C D
    → Functor
      (category-setoid C C' I)
      (category-setoid D D' J)
  functor-setoid C' D' I J F
    = record {FunctorSetoid C' D' I J F}

-- ## SetoidFunctorEqual

-- ### Definition

record SetoidFunctorEqual
  {C D : SetoidCategory}
  (F₁ F₂ : SetoidFunctor C D)
  : Set
  where

  field

    base
      : (x : SetoidCategory.Object C)
      → SetoidFunctor.base F₁ x
        ≡ SetoidFunctor.base F₂ x
    
    map
      : {x y : SetoidCategory.Object C}
      → (f : SetoidCategory.Arrow C x y)
      → SetoidCategory.ArrowEqual' D
        (SetoidFunctor.map F₁ f)
        (SetoidFunctor.map F₂ f)

-- ### Symmetry

module _
  {C D : SetoidCategory}
  {F₁ F₂ : SetoidFunctor C D}
  where

  module SetoidFunctorSym
    (p : SetoidFunctorEqual F₁ F₂)
    where

    base
      : (x : SetoidCategory.Object C)
      → SetoidFunctor.base F₂ x
        ≡ SetoidFunctor.base F₁ x
    base x
      = sym
        (SetoidFunctorEqual.base p x)
    
    map
      : {x y : SetoidCategory.Object C}
      → (f : SetoidCategory.Arrow C x y)
      → SetoidCategory.ArrowEqual' D
        (SetoidFunctor.map F₂ f)
        (SetoidFunctor.map F₁ f)
    map f
      = SetoidCategory.arrow-sym' D
        (SetoidFunctorEqual.map p f)

  setoid-functor-sym
    : SetoidFunctorEqual F₁ F₂
    → SetoidFunctorEqual F₂ F₁
  setoid-functor-sym p
    = record {SetoidFunctorSym p}

-- ### Transitivity

module _
  {C D : SetoidCategory}
  {F₁ F₂ F₃ : SetoidFunctor C D}
  where

  module SetoidFunctorTrans
    (p₁ : SetoidFunctorEqual F₁ F₂)
    (p₂ : SetoidFunctorEqual F₂ F₃)
    where

    base
      : (x : SetoidCategory.Object C)
      → SetoidFunctor.base F₁ x
        ≡ SetoidFunctor.base F₃ x
    base x
      = trans
        (SetoidFunctorEqual.base p₁ x)
        (SetoidFunctorEqual.base p₂ x)
    
    map
      : {x y : SetoidCategory.Object C}
      → (f : SetoidCategory.Arrow C x y)
      → SetoidCategory.ArrowEqual' D
        (SetoidFunctor.map F₁ f)
        (SetoidFunctor.map F₃ f)
    map f
      = SetoidCategory.arrow-trans' D
        (SetoidFunctorEqual.map p₁ f)
        (SetoidFunctorEqual.map p₂ f)

  setoid-functor-trans
    : SetoidFunctorEqual F₁ F₂
    → SetoidFunctorEqual F₂ F₃
    → SetoidFunctorEqual F₁ F₃
  setoid-functor-trans p₁ p₂
    = record {SetoidFunctorTrans p₁ p₂}

-- ## SetoidFunctorIdentity

-- ### Definition

record SetoidFunctorIdentity
  {C : SetoidCategory}
  (F : SetoidFunctor C C)
  : Set
  where

  field

    base
      : (x : SetoidCategory.Object C)
      → SetoidFunctor.base F x ≡ x

    map
      : {x y : SetoidCategory.Object C}
      → (f : SetoidCategory.Arrow C x y)
      → SetoidCategory.ArrowEqual' C
        (SetoidFunctor.map F f) f

-- ### Equality

setoid-functor-identity-from-equal
  : {C : SetoidCategory}
  → {F : SetoidFunctor C C}
  → SetoidFunctorEqual F (setoid-functor-identity C)
  → SetoidFunctorIdentity F
setoid-functor-identity-from-equal p
  = record {SetoidFunctorEqual p}

-- ### Conversion

module _
  {C : SetoidCategory}
  {F : SetoidFunctor C C}
  where

  module FunctorIdentitySetoid
    (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    (I : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    (p : SetoidFunctorIdentity F)
    where

    open CategorySetoid
      using (from-eq'; from-to; to)

    base
      : (x : Category.Object (category-setoid C C' I))
      → Functor.base (functor-setoid C' C' I I F) x ≅ x
    base
      = SetoidFunctorIdentity.base p

    map
      : {x y : Category.Object (category-setoid C C' I)}
      → (f : Category.Arrow (category-setoid C C' I) x y)
      → Functor.map (functor-setoid C' C' I I F) f ≅ f
    map f
      = trans (from-eq' C C' I (SetoidFunctorIdentity.map p
        (to C C' I f)))
      $ from-to C C' I f

  functor-identity-setoid
    : (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    → (I : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    → SetoidFunctorIdentity F
    → FunctorIdentity
      (functor-setoid C' C' I I F)
  functor-identity-setoid C' I p
    = record {FunctorIdentitySetoid C' I p}

-- ## SetoidFunctorCompose

-- ### Definition

record SetoidFunctorCompose
  {C D E : SetoidCategory}
  (F : SetoidFunctor D E)
  (G : SetoidFunctor C D)
  (H : SetoidFunctor C E)
  : Set
  where

  field

    base
      : (x : SetoidCategory.Object C)
      → SetoidFunctor.base H x ≡ SetoidFunctor.base F (SetoidFunctor.base G x)

    map
      : {x y : SetoidCategory.Object C}
      → (f : SetoidCategory.Arrow C x y)
      → SetoidCategory.ArrowEqual' E
        (SetoidFunctor.map H f)
        (SetoidFunctor.map F (SetoidFunctor.map G f))

-- ### Equality

setoid-functor-compose-from-equal
  : {C D E : SetoidCategory}
  → {H : SetoidFunctor C E}
  → (F : SetoidFunctor D E)
  → (G : SetoidFunctor C D)
  → SetoidFunctorEqual H (setoid-functor-compose F G)
  → SetoidFunctorCompose F G H
setoid-functor-compose-from-equal _ _ p
  = record {SetoidFunctorEqual p}

-- ### Conversion

module _
  {C D E : SetoidCategory}
  {F : SetoidFunctor D E}
  {G : SetoidFunctor C D}
  {H : SetoidFunctor C E}
  where

  module FunctorComposeSetoid
    (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    (D' : SetoidCategory.Object D → SetoidCategory.Object D → Set)
    (E' : SetoidCategory.Object E → SetoidCategory.Object E → Set)
    (I : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    (J : (x y : SetoidCategory.Object D)
      → SetoidIsomorphism (D' x y) (SetoidCategory.ArrowSetoid D x y))
    (K : (x y : SetoidCategory.Object E)
      → SetoidIsomorphism (E' x y) (SetoidCategory.ArrowSetoid E x y))
    (p : SetoidFunctorCompose F G H)
    where

    open CategorySetoid
      using (from-eq; from-eq'; to; to-from)

    base
      : (x : Category.Object (category-setoid C C' I))
      → Functor.base (functor-setoid C' E' I K H) x
      ≅ Functor.base (functor-setoid D' E' J K F)
        (Functor.base (functor-setoid C' D' I J G) x)
    base
      = SetoidFunctorCompose.base p

    map
      : {x y : Category.Object (category-setoid C C' I)}
      → (f : Category.Arrow (category-setoid C C' I) x y)
      → Functor.map (functor-setoid C' E' I K H) f
      ≅ Functor.map (functor-setoid D' E' J K F)
        (Functor.map (functor-setoid C' D' I J G) f)
    map f
      = trans (from-eq' E E' K (SetoidFunctorCompose.map p
        (to C C' I f)))
      $ sym (from-eq E E' K (SetoidFunctor.map-eq F
        (to-from D D' J (SetoidFunctor.map G (to C C' I f)))))

  functor-compose-setoid
    : (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    → (D' : SetoidCategory.Object D → SetoidCategory.Object D → Set)
    → (E' : SetoidCategory.Object E → SetoidCategory.Object E → Set)
    → (I : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    → (J : (x y : SetoidCategory.Object D)
      → SetoidIsomorphism (D' x y) (SetoidCategory.ArrowSetoid D x y))
    → (K : (x y : SetoidCategory.Object E)
      → SetoidIsomorphism (E' x y) (SetoidCategory.ArrowSetoid E x y))
    → SetoidFunctorCompose F G H
    → FunctorCompose
      (functor-setoid D' E' J K F)
      (functor-setoid C' D' I J G)
      (functor-setoid C' E' I K H)
  functor-compose-setoid C' D' E' I J K p
    = record {FunctorComposeSetoid C' D' E' I J K p}

-- ## SetoidFunctorSquare

-- ### Definition

record SetoidFunctorSquare
  {C₁ C₂ D₁ D₂ : SetoidCategory}
  (F : SetoidFunctor C₁ C₂)
  (G : SetoidFunctor D₁ D₂)
  (H₁ : SetoidFunctor C₁ D₁)
  (H₂ : SetoidFunctor C₂ D₂)
  : Set
  where

  field
  
    base
      : (x₁ : SetoidCategory.Object C₁)
      → SetoidFunctor.base H₂ (SetoidFunctor.base F x₁) 
        ≡ SetoidFunctor.base G (SetoidFunctor.base H₁ x₁)

    map
      : {x₁ y₁ : SetoidCategory.Object C₁}
      → (f₁ : SetoidCategory.Arrow C₁ x₁ y₁)
      → SetoidCategory.ArrowEqual' D₂
        (SetoidFunctor.map H₂ (SetoidFunctor.map F f₁))
        (SetoidFunctor.map G (SetoidFunctor.map H₁ f₁))

-- ### Equality

setoid-functor-square-from-equal
  : {C₁ C₂ D₁ D₂ : SetoidCategory}
  → (F : SetoidFunctor C₁ C₂)
  → (G : SetoidFunctor D₁ D₂)
  → (H₁ : SetoidFunctor C₁ D₁)
  → (H₂ : SetoidFunctor C₂ D₂)
  → SetoidFunctorEqual
    (setoid-functor-compose H₂ F)
    (setoid-functor-compose G H₁)
  → SetoidFunctorSquare F G H₁ H₂
setoid-functor-square-from-equal _ _ _ _ p
  = record {SetoidFunctorEqual p}

-- ### Conversion

module _
  {C₁ C₂ D₁ D₂ : SetoidCategory}
  {F : SetoidFunctor C₁ C₂}
  {G : SetoidFunctor D₁ D₂}
  {H₁ : SetoidFunctor C₁ D₁}
  {H₂ : SetoidFunctor C₂ D₂}
  where

  module FunctorSquareSetoid
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
    (s : SetoidFunctorSquare F G H₁ H₂)
    where

    open CategorySetoid
      using (from-eq; from-eq'; to; to-from)

    base
      : (x₁ : Category.Object (category-setoid C₁ C₁' I₁))
      → Functor.base (functor-setoid C₂' D₂' I₂ J₂ H₂)
        (Functor.base (functor-setoid C₁' C₂' I₁ I₂ F) x₁) 
      ≅ Functor.base (functor-setoid D₁' D₂' J₁ J₂ G)
        (Functor.base (functor-setoid C₁' D₁' I₁ J₁ H₁) x₁)
    base
      = SetoidFunctorSquare.base s
  
    map
      : {x₁ y₁ : Category.Object (category-setoid C₁ C₁' I₁)}
      → (f₁ : Category.Arrow (category-setoid C₁ C₁' I₁) x₁ y₁)
      → Functor.map (functor-setoid C₂' D₂' I₂ J₂ H₂)
        (Functor.map (functor-setoid C₁' C₂' I₁ I₂ F) f₁)
      ≅ Functor.map (functor-setoid D₁' D₂' J₁ J₂ G)
        (Functor.map (functor-setoid C₁' D₁' I₁ J₁ H₁) f₁)
    map f₁
      = trans (from-eq D₂ D₂' J₂ (SetoidFunctor.map-eq H₂
        (to-from C₂ C₂' I₂ (SetoidFunctor.map F (to C₁ C₁' I₁ f₁)))))
      $ trans (from-eq' D₂ D₂' J₂ (SetoidFunctorSquare.map s
        (to C₁ C₁' I₁ f₁)))
      $ sym (from-eq D₂ D₂' J₂ (SetoidFunctor.map-eq G
        (to-from D₁ D₁' J₁ (SetoidFunctor.map H₁ (to C₁ C₁' I₁ f₁)))))

  functor-square-setoid
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
    → SetoidFunctorSquare F G H₁ H₂
    → FunctorSquare
      (functor-setoid C₁' C₂' I₁ I₂ F)
      (functor-setoid D₁' D₂' J₁ J₂ G)
      (functor-setoid C₁' D₁' I₁ J₁ H₁)
      (functor-setoid C₂' D₂' I₂ J₂ H₂)
  functor-square-setoid C₁' C₂' D₁' D₂' I₁ I₂ J₁ J₂ s
    = record {FunctorSquareSetoid C₁' C₂' D₁' D₂' I₁ I₂ J₁ J₂ s}

