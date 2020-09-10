module Prover.Category.Induced where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare; functor-compose'; functor-compose-from-equal;
    functor-compose-to-equal; functor-identity'; functor-identity-from-equal;
    functor-identity-to-equal; functor-square-from-equal;
    functor-square-to-equal; functor-sym; functor-trans)
open import Prover.Function
  using (Function; FunctionCompose; FunctionEqual; FunctionIdentity;
    FunctionSquare)
open import Prover.Function.Compose
  using (function-square-compose)
open import Prover.Function.Equal
  using (function-compose-to-equal; function-identity-to-equal;
    function-square-to-equal)
open import Prover.Function.Identity
  using (function-square-identity)
open import Prover.Prelude

-- ## Category

module _
  {C : Set}
  where

  module CategoryInduced
    (C' : Category)
    (F : Function C (Category.Object C'))
    where

    Object
      : Set
    Object
      = C

    record Arrow
      (x y : Object)
      : Set
      where

      constructor

        arrow

      field

        inner
          : Category.Arrow C'
            (Function.base F x)
            (Function.base F y)

    arrow-eq
      : {x₁ x₂ y₁ y₂ : Object}
      → {f₁ : Arrow x₁ y₁}
      → {f₂ : Arrow x₂ y₂}
      → x₁ ≡ x₂
      → y₁ ≡ y₂
      → Arrow.inner f₁ ≅ Arrow.inner f₂
      → f₁ ≅ f₂
    arrow-eq refl refl refl
      = refl

    identity
      : (x : Object)
      → Arrow x x
    identity x
      = arrow
      $ Category.identity C'
        (Function.base F x)

    compose
      : {x y z : Object}
      → Arrow y z
      → Arrow x y
      → Arrow x z
    compose (arrow f) (arrow g)
      = arrow
      $ Category.compose C' f g

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose f (identity x) ≡ f
    precompose (arrow f)
      = sub arrow
      $ Category.precompose C' f

    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose (identity y) f ≡ f
    postcompose (arrow f)
      = sub arrow
      $ Category.postcompose C' f

    associative
      : {w x y z : Object}
      → (f : Arrow y z)
      → (g : Arrow x y)
      → (h : Arrow w x)
      → compose (compose f g) h ≡ compose f (compose g h)
    associative (arrow f) (arrow g) (arrow h)
      = sub arrow
      $ Category.associative C' f g h

  category-induced
    : (C' : Category)
    → Function C (Category.Object C')
    → Category
  category-induced C' F
    = record {CategoryInduced C' F}

-- ## Functor

-- ### Function

module _
  {C D : Set}
  {C' D' : Category}
  {F : Function C (Category.Object C')}
  {G : Function D (Category.Object D')}
  {H : Function C D}
  where

  module FunctorInduced
    (H' : Functor C' D')
    (s : FunctionSquare F G H (Functor.function H'))
    where

    open Function H public
      using (base)

    map
      : {x y : Category.Object (category-induced C' F)}
      → Category.Arrow (category-induced C' F) x y
      → Category.Arrow (category-induced D' G) (base x) (base y)
    map {x = x} {y = y} (CategoryInduced.arrow f)
      = CategoryInduced.arrow
      $ Category.arrow D' p q
      $ Functor.map H' f
      where
        p = sym (FunctionSquare.base s x)
        q = sym (FunctionSquare.base s y)

    abstract

      map-identity
        : (x : Category.Object (category-induced C' F))
        → map (Category.identity (category-induced C' F) x)
          ≡ Category.identity (category-induced D' G) (base x)
      map-identity x
        = sub CategoryInduced.arrow
        $ trans (Category.arrow-eq D' p p
          (Functor.map H' (Category.identity C' (Function.base F x))))
        $ trans (Functor.map-identity H' (Function.base F x))
        $ sym (Category.identity-eq D' p)
        where
          p = sym (FunctionSquare.base s x)

      map-compose
        : {x y z : Category.Object (category-induced C' F)}
        → (f : Category.Arrow (category-induced C' F) y z)
        → (g : Category.Arrow (category-induced C' F) x y)
        → map (Category.compose (category-induced C' F) f g)
          ≡ Category.compose (category-induced D' G) (map f) (map g)
      map-compose {x = x} {y = y} {z = z}
        (CategoryInduced.arrow f)
        (CategoryInduced.arrow g)
        = sub CategoryInduced.arrow
        $ trans (Category.arrow-eq D' p r
          (Functor.map H' (Category.compose C' f g)))
        $ trans (Functor.map-compose H' f g)
        $ sym (Category.compose-eq D' p q r
          (Category.arrow-eq D' q r (Functor.map H' f))
          (Category.arrow-eq D' p q (Functor.map H' g)))
        where
          p = sym (FunctionSquare.base s x)
          q = sym (FunctionSquare.base s y)
          r = sym (FunctionSquare.base s z)

  functor-induced
    : (H' : Functor C' D')
    → FunctionSquare F G H (Functor.function H')
    → Functor
      (category-induced C' F)
      (category-induced D' G)
  functor-induced H' s
    = record {FunctorInduced H' s}

-- ### Identity

module _
  {C : Set}
  where

  module FunctorInducedIdentity
    (C' : Category)
    (F : Function C (Category.Object C'))
    where

    base
      : (x : Category.Object (category-induced C' F))
      → Functor.base
        (functor-induced
          (functor-identity' C')
          (function-square-identity F)) x
      ≅ Functor.base
        (functor-identity'
          (category-induced C' F)) x
    base _
      = refl
  
    map
      : {x y : Category.Object (category-induced C' F)}
      → (f : Category.Arrow (category-induced C' F) x y)
      → Functor.map
        (functor-induced
          (functor-identity' C')
          (function-square-identity F)) f
      ≅ Functor.map
        (functor-identity'
          (category-induced C' F)) f
    map _
      = refl

  functor-induced-identity
    : (C' : Category)
    → (F : Function C (Category.Object C'))
    → FunctorEqual
      (functor-induced
        (functor-identity' C')
        (function-square-identity F))
      (functor-identity'
        (category-induced C' F))
  functor-induced-identity C' F
    = record {FunctorInducedIdentity C' F}

-- ### Compose

module _
  {C D E : Set}
  {C' D' E' : Category}
  {F : Function C (Category.Object C')}
  {G : Function D (Category.Object D')}
  {H : Function E (Category.Object E')}
  {I : Function D E}
  {J : Function C D}
  where

  module FunctorInducedCompose
    (I' : Functor D' E')
    (J' : Functor C' D')
    (s : FunctionSquare G H I (Functor.function I'))
    (t : FunctionSquare F G J (Functor.function J'))
    where

    base
      : (x : Category.Object (category-induced C' F))
      → Functor.base
        (functor-induced
          (functor-compose' I' J')
          (function-square-compose s t)) x
      ≅ Functor.base
        (functor-compose'
          (functor-induced I' s)
          (functor-induced J' t)) x
    base _
      = refl
  
    map
      : {x y : Category.Object (category-induced C' F)}
      → (f : Category.Arrow (category-induced C' F) x y)
      → Functor.map
        (functor-induced
          (functor-compose' I' J')
          (function-square-compose s t)) f
      ≅ Functor.map
        (functor-compose'
          (functor-induced I' s)
          (functor-induced J' t)) f
    map {x = x} {y = y} (CategoryInduced.arrow f)
      = sub CategoryInduced.arrow
      $ trans (Category.arrow-eq E'
        (sym (FunctionSquare.base (function-square-compose s t) x))
        (sym (FunctionSquare.base (function-square-compose s t) y))
        (Functor.map I' (Functor.map J' f)))
      $ trans (Functor.map-eq I' p q (sym (Category.arrow-eq D' (sym p) (sym q)
        (Functor.map J' f))))
      $ sym (Category.arrow-eq E'
        (sym (FunctionSquare.base s (Function.base J x)))
        (sym (FunctionSquare.base s (Function.base J y)))
        (Functor.map I' (Category.arrow D' (sym p) (sym q) (Functor.map J' f))))
      where
        p = FunctionSquare.base t x
        q = FunctionSquare.base t y

  functor-induced-compose
    : (I' : Functor D' E')
    → (J' : Functor C' D')
    → (s : FunctionSquare G H I (Functor.function I'))
    → (t : FunctionSquare F G J (Functor.function J'))
    → FunctorEqual
      (functor-induced
        (functor-compose' I' J')
        (function-square-compose s t))
      (functor-compose'
        (functor-induced I' s)
        (functor-induced J' t))
  functor-induced-compose I' J' s t
    = record {FunctorInducedCompose I' J' s t}

-- ## Functor'

module _
  {C : Set}
  where

  module FunctorInduced'
    (C' : Category)
    (F : Function C (Category.Object C'))
    where

    open Function F public
      using (base)

    map
      : {x y : Category.Object (category-induced C' F)}
      → Category.Arrow (category-induced C' F) x y
      → Category.Arrow C' (base x) (base y)
    map
      = CategoryInduced.Arrow.inner

    abstract

      map-identity
        : (x : Category.Object (category-induced C' F))
        → map (Category.identity (category-induced C' F) x)
          ≡ Category.identity C' (base x)
      map-identity _
        = refl

      map-compose
        : {x y z : Category.Object (category-induced C' F)}
        → (f : Category.Arrow (category-induced C' F) y z)
        → (g : Category.Arrow (category-induced C' F) x y)
        → map (Category.compose (category-induced C' F) f g)
          ≡ Category.compose C' (map f) (map g)
      map-compose _ _
        = refl

  functor-induced'
    : (C' : Category)
    → (F : Function C (Category.Object C'))
    → Functor
      (category-induced C' F) C'
  functor-induced' C' F
    = record {FunctorInduced' C' F}

-- ## FunctorEqual

module _
  {C D : Set}
  {C' D' : Category}
  {F : Function C (Category.Object C')}
  {G : Function D (Category.Object D')}
  {H₁ H₂ : Function C D}
  {H₁' H₂' : Functor C' D'}
  where

  module FunctorEqualInduced
    (s₁ : FunctionSquare F G H₁ (Functor.function H₁'))
    (s₂ : FunctionSquare F G H₂ (Functor.function H₂'))
    (p₁ : FunctionEqual H₁ H₂)
    (p₂ : FunctorEqual H₁' H₂')
    where

    open FunctionEqual p₁ public
      using (base)

    map
      : {x y : Category.Object (category-induced C' F)}
      → (f : Category.Arrow (category-induced C' F) x y)
      → Functor.map (functor-induced H₁' s₁) f
        ≅ Functor.map (functor-induced H₂' s₂) f
    map {x = x} {y = y} (CategoryInduced.arrow f)
      = CategoryInduced.arrow-eq D' G
        (FunctionEqual.base p₁ x)
        (FunctionEqual.base p₁ y)
      $ trans (Category.arrow-eq D'
        (sym (FunctionSquare.base s₁ x))
        (sym (FunctionSquare.base s₁ y))
        (Functor.map H₁' f))
      $ trans (FunctorEqual.map p₂ f)
      $ sym (Category.arrow-eq D'
        (sym (FunctionSquare.base s₂ x))
        (sym (FunctionSquare.base s₂ y))
        (Functor.map H₂' f))

  functor-equal-induced
    : (s₁ : FunctionSquare F G H₁ (Functor.function H₁'))
    → (s₂ : FunctionSquare F G H₂ (Functor.function H₂'))
    → FunctionEqual H₁ H₂
    → FunctorEqual H₁' H₂'
    → FunctorEqual
      (functor-induced H₁' s₁)
      (functor-induced H₂' s₂)
  functor-equal-induced s₁ s₂ p₁ p₂
    = record {FunctorEqualInduced s₁ s₂ p₁ p₂}

-- ## FunctorIdentity

functor-identity-induced
  : {C : Set}
  → {C' : Category}
  → {F : Function C (Category.Object C')}
  → {G : Function C C}
  → {G' : Functor C' C'}
  → (s : FunctionSquare F F G (Functor.function G'))
  → FunctionIdentity G
  → FunctorIdentity G'
  → FunctorIdentity
    (functor-induced G' s)
functor-identity-induced
  {C' = C'} {F = F} s p p'
  = functor-identity-from-equal
  $ functor-trans (functor-equal-induced s
    (function-square-identity F)
    (function-identity-to-equal p)
    (functor-identity-to-equal p'))
  $ functor-induced-identity C' F

-- ## FunctorCompose

functor-compose-induced
  : {C D E : Set}
  → {C' D' E' : Category}
  → {F : Function C (Category.Object C')}
  → {G : Function D (Category.Object D')}
  → {H : Function E (Category.Object E')}
  → {I : Function D E}
  → {J : Function C D}
  → {K : Function C E}
  → {I' : Functor D' E'}
  → {J' : Functor C' D'}
  → {K' : Functor C' E'}
  → (s : FunctionSquare G H I (Functor.function I'))
  → (t : FunctionSquare F G J (Functor.function J'))
  → (u : FunctionSquare F H K (Functor.function K'))
  → FunctionCompose I J K
  → FunctorCompose I' J' K'
  → FunctorCompose 
    (functor-induced I' s)
    (functor-induced J' t)
    (functor-induced K' u)
functor-compose-induced
  {I' = I'} {J' = J'} s t u p p'
  = functor-compose-from-equal
    (functor-induced I' s)
    (functor-induced J' t)
  $ functor-trans (functor-equal-induced u
    (function-square-compose s t)
    (function-compose-to-equal p)
    (functor-compose-to-equal p'))
  $ functor-induced-compose I' J' s t

-- ## FunctorSquare

functor-square-induced
  : {C₁ C₂ D₁ D₂ : Set}
  → {C₁' C₂' D₁' D₂' : Category}
  → {F₁ : Function C₁ (Category.Object C₁')}
  → {F₂ : Function C₂ (Category.Object C₂')}
  → {G₁ : Function D₁ (Category.Object D₁')}
  → {G₂ : Function D₂ (Category.Object D₂')}
  → {H : Function C₁ C₂}
  → {I : Function D₁ D₂}
  → {J₁ : Function C₁ D₁}
  → {J₂ : Function C₂ D₂}
  → {H' : Functor C₁' C₂'}
  → {I' : Functor D₁' D₂'}
  → {J₁' : Functor C₁' D₁'}
  → {J₂' : Functor C₂' D₂'}
  → (s : FunctionSquare F₁ F₂ H (Functor.function H'))
  → (t : FunctionSquare G₁ G₂ I (Functor.function I'))
  → (u₁ : FunctionSquare F₁ G₁ J₁ (Functor.function J₁'))
  → (u₂ : FunctionSquare F₂ G₂ J₂ (Functor.function J₂'))
  → FunctionSquare H I J₁ J₂
  → FunctorSquare H' I' J₁' J₂'
  → FunctorSquare
    (functor-induced H' s)
    (functor-induced I' t)
    (functor-induced J₁' u₁)
    (functor-induced J₂' u₂)
functor-square-induced
  {H' = H'} {I' = I'} {J₁' = J₁'} {J₂' = J₂'} s t u₁ u₂ v v'
  = functor-square-from-equal
    (functor-induced H' s)
    (functor-induced I' t)
    (functor-induced J₁' u₁)
    (functor-induced J₂' u₂)
  $ functor-trans (functor-sym
    (functor-induced-compose J₂' H' u₂ s))
  $ functor-trans (functor-equal-induced
    (function-square-compose u₂ s)
    (function-square-compose t u₁)
    (function-square-to-equal v)
    (functor-square-to-equal v'))
  $ functor-induced-compose I' J₁' t u₁

-- ## FunctorSquare'

module _
  {C₁ C₂ : Set}
  {C₁' C₂' : Category}
  {F₁ : Function C₁ (Category.Object C₁')}
  {F₂ : Function C₂ (Category.Object C₂')}
  {G : Function C₁ C₂}
  where

  module FunctorSquareInduced'
    (G' : Functor C₁' C₂')
    (s : FunctionSquare F₁ F₂ G (Functor.function G'))
    where

    base
      : (x₁ : Category.Object (category-induced C₁' F₁))
      → Functor.base (functor-induced' C₂' F₂)
        (Functor.base (functor-induced G' s) x₁) 
      ≅ Functor.base G'
        (Functor.base (functor-induced' C₁' F₁) x₁)
    base x₁
      = sym (FunctionSquare.base s x₁)

    map
      : {x₁ y₁ : Category.Object (category-induced C₁' F₁)}
      → (f₁ : Category.Arrow (category-induced C₁' F₁) x₁ y₁)
      → Functor.map (functor-induced' C₂' F₂)
        (Functor.map (functor-induced G' s) f₁)
      ≅ Functor.map G'
        (Functor.map (functor-induced' C₁' F₁) f₁)
    map {x₁ = x₁} {y₁ = y₁} (CategoryInduced.arrow f₁)
      = Category.arrow-eq C₂' (base x₁) (base y₁) (Functor.map G' f₁)

  functor-square-induced'
    : (G' : Functor C₁' C₂')
    → (s : FunctionSquare F₁ F₂ G (Functor.function G'))
    → FunctorSquare
      (functor-induced G' s) G'
      (functor-induced' C₁' F₁)
      (functor-induced' C₂' F₂)
  functor-square-induced' G' s
    = record {FunctorSquareInduced' G' s}

