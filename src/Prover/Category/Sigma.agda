module Prover.Category.Sigma where

open import Prover.Category
  using (module Category'; Category; Functor; FunctorCompose; FunctorEqual;
    FunctorIdentity; FunctorSquare; functor-compose';
    functor-compose-from-equal; functor-compose-to-equal; functor-identity';
    functor-identity-from-equal; functor-identity-to-equal;
    functor-square-from-equal; functor-square-to-equal; functor-sym;
    functor-trans)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor; Dependent₁FunctorCompose;
    Dependent₁FunctorEqual; Dependent₁FunctorIdentity; Dependent₁FunctorSquare;
    dependent₁-functor-compose; dependent₁-functor-compose-to-equal;
    dependent₁-functor-identity; dependent₁-functor-identity-to-equal;
    dependent₁-functor-square-to-equal)
open import Prover.Prelude

-- ## Category

-- ### Function

module _
  {C₁ : Category}
  where

  module CategorySigma
    (C₂ : Dependent₁Category C₁)
    where

    Object
      : Set
    Object
      = x₁ ∈ Category.Object C₁
      × Dependent₁Category.Object C₂ x₁
  
    record Arrow
      (x y : Object)
      : Set
      where
  
      constructor
        
        arrow
  
      field
  
        {domain}
          : Dependent₁Category.Object C₂ (π₁ y)
  
        arrow₁
          : Category.Arrow C₁ (π₁ x) (π₁ y)
  
        arrow₂
          : Dependent₁Category.Arrow C₂ (π₁ y) domain (π₂ y)
  
        valid
          : Dependent₁Category.base C₂ arrow₁ (π₂ x) ≡ domain
  
    record ArrowEqual
      {x y : Object}
      (f₁ f₂ : Arrow x y)
      : Set
      where

      constructor

        arrow-equal

      field

        arrow₁
          : Category.ArrowEqual C₁
            (Arrow.arrow₁ f₁)
            (Arrow.arrow₁ f₂)

        arrow₂
          : Dependent₁Category.ArrowEqual' C₂ (π₁ y)
            (Arrow.arrow₂ f₁)
            (Arrow.arrow₂ f₂)

    abstract

      arrow-refl
        : {x y : Object}
        → {f : Arrow x y}
        → ArrowEqual f f
      arrow-refl {y = (y₁ , _)}
        = record
        { arrow₁
          = Category.arrow-refl C₁
        ; arrow₂
          = Dependent₁Category.arrow-refl' C₂ y₁
        }

      arrow-sym
        : {x y : Object}
        → {f₁ f₂ : Arrow x y}
        → ArrowEqual f₁ f₂
        → ArrowEqual f₂ f₁
      arrow-sym {y = (y₁ , _)}
        (arrow-equal p₁ p₂)
        = record
        { arrow₁
          = Category.arrow-sym C₁ p₁
        ; arrow₂
          = Dependent₁Category.arrow-sym' C₂ y₁ p₂
        }

      arrow-trans
        : {x y : Object}
        → {f₁ f₂ f₃ : Arrow x y}
        → ArrowEqual f₁ f₂
        → ArrowEqual f₂ f₃
        → ArrowEqual f₁ f₃
      arrow-trans {y = (y₁ , _)}
        (arrow-equal p₁₁ p₁₂)
        (arrow-equal p₂₁ p₂₂)
        = record
        { arrow₁
          = Category.arrow-trans C₁ p₁₁ p₂₁
        ; arrow₂
          = Dependent₁Category.arrow-trans' C₂ y₁ p₁₂ p₂₂
        }

      simplify
        : {x y : Object}
        → Arrow x y
        → Arrow x y
      simplify {x = (_ , x₂)} {y = (y₁ , _)}
        (arrow f₁ f₂ p₂)
        = record
        { arrow₁
          = Category.simplify C₁ f₁
        ; arrow₂
          = Dependent₁Category.simplify C₂ y₁ f₂
        ; valid
          = trans (Dependent₁Category.base-equal C₂
            (Category.simplify-equal C₁ f₁) x₂) p₂
        }

      simplify-equal
        : {x y : Object}
        → (f : Arrow x y)
        → ArrowEqual
          (simplify f) f
      simplify-equal {y = (y₁ , _)}
        (arrow f₁ f₂ _)
        = record
        { arrow₁
          = Category.simplify-equal C₁ f₁
        ; arrow₂
          = Dependent₁Category.simplify-equal' C₂ y₁ f₂
        }

    identity
      : (x : Object)
      → Arrow x x
    identity (x₁ , x₂)
      = record
      { arrow₁
        = Category.identity C₁ x₁
      ; arrow₂
        = Dependent₁Category.identity C₂ x₁ x₂
      ; valid
        = Dependent₁Category.base-identity C₂ x₁ x₂
      }
  
    compose
      : {x y z : Object}
      → Arrow y z
      → Arrow x y
      → Arrow x z
    compose {x = (_ , x₂)} {z = (z₁ , _)}
      (arrow f₁ f₂ p₂)
      (arrow g₁ g₂ q₂)
      = record
      { arrow₁
        = Category.compose C₁ f₁ g₁
      ; arrow₂
        = Dependent₁Category.compose' C₂ z₁ p₂ f₂
          (Dependent₁Category.map C₂ f₁ g₂)
      ; valid
        = trans (Dependent₁Category.base-compose C₂ f₁ g₁ x₂)
        $ sub (Dependent₁Category.base C₂ f₁) q₂
      }
  
    abstract

      compose-equal
        : {x y z : Object}
        → {f₁ f₂ : Arrow y z}
        → {g₁ g₂ : Arrow x y}
        → ArrowEqual f₁ f₂
        → ArrowEqual g₁ g₂
        → ArrowEqual
          (compose f₁ g₁)
          (compose f₂ g₂)
      compose-equal {z = (z₁ , _)}
        {f₁ = arrow _ _ refl}
        {f₂ = arrow _ _ refl}
        (arrow-equal p₁ p₂)
        (arrow-equal q₁ q₂)
        = record
        { arrow₁
          = Category.compose-equal C₁ p₁ q₁
        ; arrow₂
          = Dependent₁Category.compose-equal' C₂ z₁ p₂
            (Dependent₁Category.map-equal C₂ p₁ q₂)
        }

      precompose
        : {x y : Object}
        → (f : Arrow x y)
        → ArrowEqual
          (compose f (identity x)) f
      precompose {x = (_ , x₂)} {y = (y₁ , _)}
        (arrow f₁ f₂ refl)
        = record
        { arrow₁
          = Category.precompose C₁ f₁
        ; arrow₂
          = Dependent₁Category.arrow-trans' C₂ y₁
            (Dependent₁Category.compose-equal' C₂ y₁
              (Dependent₁Category.arrow-refl' C₂ y₁)
              (Dependent₁Category.map-identity' C₂ f₁ x₂))
          $ Dependent₁Category.precompose' C₂ y₁ f₂
        }
    
      postcompose
        : {x y : Object}
        → (f : Arrow x y)
        → ArrowEqual
          (compose (identity y) f) f
      postcompose {y = (y₁ , y₂)}
        (arrow f₁ f₂ refl)
        = record
        { arrow₁
          = Category.postcompose C₁ f₁
        ; arrow₂
          = Dependent₁Category.arrow-trans' C₂ y₁
            (Dependent₁Category.compose-equal'' C₂ y₁
              (Dependent₁Category.base-identity C₂ y₁ y₂)
              (Dependent₁Category.identity C₂ y₁ y₂)
              (Dependent₁Category.map-identity C₂ y₁ f₂))
          $ Dependent₁Category.postcompose' C₂ y₁ f₂
        }

      associative
        : {w x y z : Object}
        → (f : Arrow y z)
        → (g : Arrow x y)
        → (h : Arrow w x)
        → ArrowEqual
          (compose (compose f g) h)
          (compose f (compose g h))
      associative {x = (_ , x₂)} {z = (z₁ , _)}
        (arrow f₁ f₂ refl)
        (arrow g₁ g₂ refl)
        (arrow h₁ h₂ refl)
        = record
        { arrow₁
          = Category.associative C₁ f₁ g₁ h₁
        ; arrow₂
          = Dependent₁Category.arrow-trans' C₂ z₁
            (Dependent₁Category.compose-equal'' C₂ z₁
              (trans (Dependent₁Category.base-compose C₂ f₁ g₁ x₂) refl)
              (Dependent₁Category.compose C₂ z₁ f₂
                (Dependent₁Category.map C₂ f₁ g₂))
              (Dependent₁Category.map-compose C₂ f₁ g₁ h₂))
          $ Dependent₁Category.arrow-trans' C₂ z₁
            (Dependent₁Category.associative' C₂ z₁ f₂
              (Dependent₁Category.map C₂ f₁ g₂)
              (Dependent₁Category.map C₂ f₁
                (Dependent₁Category.map C₂ g₁ h₂)))
          $ Dependent₁Category.arrow-sym' C₂ z₁
            (Dependent₁Category.compose-equal' C₂ z₁
              (Dependent₁Category.arrow-refl' C₂ z₁)
              (Dependent₁Category.map-compose' C₂ f₁ g₂
                (Dependent₁Category.map C₂ g₁ h₂)))
        }

  category-sigma
    : Dependent₁Category C₁
    → Category
  category-sigma C₂
    = record {CategorySigma C₂}

-- ### Equality

arrow-equal-sigma
  : {C₁ : Category}
  → (C₂ : Dependent₁Category C₁)
  → {x₁₁ x₂₁ y₁₁ y₂₁ : Category.Object C₁}
  → {x₁₂ : Dependent₁Category.Object C₂ x₁₁}
  → {x₂₂ : Dependent₁Category.Object C₂ x₂₁}
  → {y₁₂ y₁₂' : Dependent₁Category.Object C₂ y₁₁}
  → {y₂₂ y₂₂' : Dependent₁Category.Object C₂ y₂₁}
  → {f₁₁ : Category.Arrow C₁ x₁₁ y₁₁}
  → {f₂₁ : Category.Arrow C₁ x₂₁ y₂₁}
  → {f₁₂ : Dependent₁Category.Arrow C₂ y₁₁ y₁₂' y₁₂}
  → {f₂₂ : Dependent₁Category.Arrow C₂ y₂₁ y₂₂' y₂₂}
  → {p₁₂ : Dependent₁Category.base C₂ f₁₁ x₁₂ ≡ y₁₂'}
  → {p₂₂ : Dependent₁Category.base C₂ f₂₁ x₂₂ ≡ y₂₂'}
  → x₁₂ ≅ x₂₂
  → Category.ArrowEqual' C₁ f₁₁ f₂₁
  → Category'.ArrowEqual'
    (Dependent₁Category.category C₂ y₁₁)
    (Dependent₁Category.category C₂ y₂₁) f₁₂ f₂₂
  → Category.ArrowEqual'
    (category-sigma C₂)
    (CategorySigma.arrow f₁₁ f₁₂ p₁₂)
    (CategorySigma.arrow f₂₁ f₂₂ p₂₂)
arrow-equal-sigma _ refl (Category.any q₁) q₂@(Category.any _)
  = Category.any (CategorySigma.arrow-equal q₁ q₂)

-- ## Functor

-- ### Function

module _
  {C₁ D₁ : Category}
  {C₂ : Dependent₁Category C₁}
  {D₂ : Dependent₁Category D₁}
  {F₁ : Functor C₁ D₁}
  where

  module FunctorSigma
    (F₂ : Dependent₁Functor C₂ D₂ F₁)
    where

    base
      : Category.Object (category-sigma C₂)
      → Category.Object (category-sigma D₂)
    base (x₁ , x₂)
      = Functor.base F₁ x₁
      , Dependent₁Functor.base F₂ x₁ x₂

    map
      : {x y : Category.Object (category-sigma C₂)}
      → Category.Arrow (category-sigma C₂) x y
      → Category.Arrow (category-sigma D₂) (base x) (base y)
    map {x = (_ , x₂)} {y = (y₁ , _)}
      (CategorySigma.arrow f₁ f₂ p₂)
      = record
      { arrow₁
        = Functor.map F₁ f₁
      ; arrow₂
        = Dependent₁Functor.map F₂ y₁ f₂
      ; valid
        = trans (sym (Dependent₁Functor.base-square F₂ f₁ x₂))
        $ sub (Dependent₁Functor.base F₂ y₁) p₂
      }

    abstract

      map-equal
        : {x y : Category.Object (category-sigma C₂)}
        → {f₁ f₂ : Category.Arrow (category-sigma C₂) x y}
        → Category.ArrowEqual (category-sigma C₂) f₁ f₂
        → Category.ArrowEqual (category-sigma D₂) (map f₁) (map f₂)
      map-equal {y = (y₁ , _)}
        (CategorySigma.arrow-equal p₁ p₂)
        = record
        { arrow₁
          = Functor.map-equal F₁ p₁
        ; arrow₂
          = Dependent₁Functor.map-equal F₂ y₁ p₂
        }

      map-identity
        : (x : Category.Object (category-sigma C₂))
        → Category.ArrowEqual (category-sigma D₂)
          (map (Category.identity (category-sigma C₂) x))
          (Category.identity (category-sigma D₂) (base x))
      map-identity (x₁ , x₂)
        = record
        { arrow₁
          = Functor.map-identity F₁ x₁
        ; arrow₂
          = Dependent₁Functor.map-identity F₂ x₁ x₂
        }
  
      map-compose
        : {x y z : Category.Object (category-sigma C₂)}
        → (f : Category.Arrow (category-sigma C₂) y z)
        → (g : Category.Arrow (category-sigma C₂) x y)
        → Category.ArrowEqual (category-sigma D₂)
          (map (Category.compose (category-sigma C₂) f g))
          (Category.compose (category-sigma D₂) (map f) (map g))
      map-compose {y = (_ , y₂)} {z = (z₁ , _)}
        (CategorySigma.arrow f₁ f₂ refl)
        (CategorySigma.arrow g₁ g₂ refl)
        = record
        { arrow₁
          = Functor.map-compose F₁ f₁ g₁
        ; arrow₂
          = Dependent₁Category.arrow-trans' D₂ (Functor.base F₁ z₁)
            (Dependent₁Functor.map-compose F₂ z₁ f₂
              (Dependent₁Category.map C₂ f₁ g₂))
          $ Dependent₁Category.arrow-sym' D₂ (Functor.base F₁ z₁)
            (Dependent₁Category.compose-equal'' D₂ (Functor.base F₁ z₁)
              (trans (sym (Dependent₁Functor.base-square F₂ f₁ y₂)) refl)
              (Dependent₁Functor.map F₂ z₁ f₂)
              (Dependent₁Category.arrow-sym' D₂ (Functor.base F₁ z₁)
                (Dependent₁Functor.map-square F₂ f₁ g₂)))
        }

  functor-sigma
    : Dependent₁Functor C₂ D₂ F₁
    → Functor
      (category-sigma C₂)
      (category-sigma D₂)
  functor-sigma F₂
    = record {FunctorSigma F₂}

-- ### Identity

module _
  {C₁ : Category}
  where

  module FunctorSigmaIdentity
    (C₂ : Dependent₁Category C₁)
    where

    base
      : (x : Category.Object (category-sigma C₂))
      → Functor.base (functor-sigma (dependent₁-functor-identity C₂)) x
        ≅ Functor.base (functor-identity' (category-sigma C₂)) x
    base _
      = refl
  
    map
      : {x y : Category.Object (category-sigma C₂)}
      → (f : Category.Arrow (category-sigma C₂) x y)
      → Category'.ArrowEqual'
        (category-sigma C₂)
        (category-sigma C₂)
        (Functor.map (functor-sigma (dependent₁-functor-identity C₂)) f)
        (Functor.map (functor-identity' (category-sigma C₂)) f)
    map {y = (y₁ , _)} _
      = arrow-equal-sigma C₂ refl
        (Category.arrow-refl' C₁)
        (Dependent₁Category.arrow-refl' C₂ y₁)

  functor-sigma-identity
    : (C₂ : Dependent₁Category C₁)
    → FunctorEqual
      (functor-sigma (dependent₁-functor-identity C₂))
      (functor-identity' (category-sigma C₂))
  functor-sigma-identity C₂
    = record {FunctorSigmaIdentity C₂}

-- ### Compose

module _
  {C₁ D₁ E₁ : Category}
  {C₂ : Dependent₁Category C₁}
  {D₂ : Dependent₁Category D₁}
  {E₂ : Dependent₁Category E₁}
  {F₁ : Functor D₁ E₁}
  {G₁ : Functor C₁ D₁}
  where

  module FunctorSigmaCompose
    (F₂ : Dependent₁Functor D₂ E₂ F₁)
    (G₂ : Dependent₁Functor C₂ D₂ G₁)
    where

    base
      : (x : Category.Object (category-sigma C₂))
      → Functor.base
        (functor-sigma (dependent₁-functor-compose F₂ G₂)) x
      ≅ Functor.base
        (functor-compose' (functor-sigma F₂) (functor-sigma G₂)) x
    base _
      = refl
  
    map
      : {x y : Category.Object (category-sigma C₂)}
      → (f : Category.Arrow (category-sigma C₂) x y)
      → Category'.ArrowEqual'
        (category-sigma E₂)
        (category-sigma E₂)
        (Functor.map
          (functor-sigma (dependent₁-functor-compose F₂ G₂)) f)
        (Functor.map
          (functor-compose' (functor-sigma F₂) (functor-sigma G₂)) f)
    map {y = (y₁ , _)} _
      = arrow-equal-sigma E₂ refl
        (Category.arrow-refl' E₁)
        (Dependent₁Category.arrow-refl' E₂
          (Functor.base F₁ (Functor.base G₁ y₁)))

  functor-sigma-compose
    : (F₂ : Dependent₁Functor D₂ E₂ F₁)
    → (G₂ : Dependent₁Functor C₂ D₂ G₁)
    → FunctorEqual
      (functor-sigma (dependent₁-functor-compose F₂ G₂))
      (functor-compose' (functor-sigma F₂) (functor-sigma G₂))
  functor-sigma-compose F₂ G₂
    = record {FunctorSigmaCompose F₂ G₂}

-- ## Functor₁

module _
  {C₁ : Category}
  where

  module FunctorSigma₁
    (C₂ : Dependent₁Category C₁)
    where

    base
      : Category.Object (category-sigma C₂)
      → Category.Object C₁
    base (x₁ , _)
      = x₁

    map
      : {x₁ y₁ : Category.Object (category-sigma C₂)}
      → Category.Arrow (category-sigma C₂) x₁ y₁
      → Category.Arrow C₁ (base x₁) (base y₁)
    map (CategorySigma.arrow f₁ _ _)
      = f₁

    abstract

      map-equal
        : {x y : Category.Object (category-sigma C₂)}
        → {f₁ f₂ : Category.Arrow (category-sigma C₂) x y}
        → Category.ArrowEqual (category-sigma C₂) f₁ f₂
        → Category.ArrowEqual C₁ (map f₁) (map f₂)
      map-equal (CategorySigma.arrow-equal p₁ _)
        = p₁

      map-identity
        : (x₁ : Category.Object (category-sigma C₂))
        → Category.ArrowEqual C₁
          (map (Category.identity (category-sigma C₂) x₁))
          (Category.identity C₁ (base x₁))
      map-identity _
        = Category.arrow-refl C₁
  
      map-compose
        : {x₁ y₁ z₁ : Category.Object (category-sigma C₂)}
        → (f₁ : Category.Arrow (category-sigma C₂) y₁ z₁)
        → (g₁ : Category.Arrow (category-sigma C₂) x₁ y₁)
        → Category.ArrowEqual C₁
          (map (Category.compose (category-sigma C₂) f₁ g₁))
          (Category.compose C₁ (map f₁) (map g₁))
      map-compose _ _
        = Category.arrow-refl C₁
  
  functor-sigma₁
    : (C₂ : Dependent₁Category C₁)
    → Functor (category-sigma C₂) C₁
  functor-sigma₁ C₂
    = record {FunctorSigma₁ C₂}

-- ## FunctorEqual

module _
  {C₁ D₁ : Category}
  {C₂ : Dependent₁Category C₁}
  {D₂ : Dependent₁Category D₁}
  {F₁₁ F₂₁ : Functor C₁ D₁}
  {F₁₂ : Dependent₁Functor C₂ D₂ F₁₁}
  {F₂₂ : Dependent₁Functor C₂ D₂ F₂₁}
  where
  
  module FunctorEqualSigma
    (p₁ : FunctorEqual F₁₁ F₂₁)
    (p₂ : Dependent₁FunctorEqual F₁₂ F₂₂)
    where

    base
      : (x : Category.Object (category-sigma C₂))
      → Functor.base (functor-sigma F₁₂) x ≅ Functor.base (functor-sigma F₂₂) x
    base (x₁ , x₂)
      = Sigma.comma-equal
        (FunctorEqual.base p₁ x₁)
        (Dependent₁FunctorEqual.base p₂ x₁ x₂)
  
    map
      : {x y : Category.Object (category-sigma C₂)}
      → (f : Category.Arrow (category-sigma C₂) x y)
      → Category'.ArrowEqual'
        (category-sigma D₂)
        (category-sigma D₂)
        (Functor.map (functor-sigma F₁₂) f)
        (Functor.map (functor-sigma F₂₂) f)
    map {x = (x₁ , x₂)} {y = (y₁ , _)} (CategorySigma.arrow f₁ f₂ _)
      = arrow-equal-sigma D₂
        (Dependent₁FunctorEqual.base p₂ x₁ x₂)
        (FunctorEqual.map p₁ f₁)
        (Dependent₁FunctorEqual.map p₂ y₁ f₂)

  functor-equal-sigma
    : FunctorEqual F₁₁ F₂₁
    → Dependent₁FunctorEqual F₁₂ F₂₂
    → FunctorEqual
      (functor-sigma F₁₂)
      (functor-sigma F₂₂)
  functor-equal-sigma p₁ p₂
    = record {FunctorEqualSigma p₁ p₂}

-- ## FunctorIdentity

functor-identity-sigma
  : {C₁ : Category}
  → {C₂ : Dependent₁Category C₁}
  → {F₁ : Functor C₁ C₁}
  → {F₂ : Dependent₁Functor C₂ C₂ F₁}
  → FunctorIdentity F₁
  → Dependent₁FunctorIdentity F₂
  → FunctorIdentity
    (functor-sigma F₂)
functor-identity-sigma {C₂ = C₂} p₁ p₂
  = functor-identity-from-equal
  $ functor-trans (functor-equal-sigma
    (functor-identity-to-equal p₁)
    (dependent₁-functor-identity-to-equal p₂))
  $ functor-sigma-identity C₂

-- ## FunctorCompose

functor-compose-sigma
  : {C₁ D₁ E₁ : Category}
  → {C₂ : Dependent₁Category C₁}
  → {D₂ : Dependent₁Category D₁}
  → {E₂ : Dependent₁Category E₁}
  → {F₁ : Functor D₁ E₁}
  → {G₁ : Functor C₁ D₁}
  → {H₁ : Functor C₁ E₁}
  → {F₂ : Dependent₁Functor D₂ E₂ F₁}
  → {G₂ : Dependent₁Functor C₂ D₂ G₁}
  → {H₂ : Dependent₁Functor C₂ E₂ H₁}
  → FunctorCompose F₁ G₁ H₁
  → Dependent₁FunctorCompose F₂ G₂ H₂
  → FunctorCompose
    (functor-sigma F₂)
    (functor-sigma G₂)
    (functor-sigma H₂)
functor-compose-sigma {F₂ = F₂} {G₂ = G₂} p₁ p₂
  = functor-compose-from-equal
    (functor-sigma F₂)
    (functor-sigma G₂)
  $ functor-trans (functor-equal-sigma
    (functor-compose-to-equal p₁)
    (dependent₁-functor-compose-to-equal p₂))
  $ functor-sigma-compose F₂ G₂

-- ## FunctorSquare

functor-square-sigma
  : {C₁₁ C₂₁ D₁₁ D₂₁ : Category}
  → {C₁₂ : Dependent₁Category C₁₁}
  → {C₂₂ : Dependent₁Category C₂₁}
  → {D₁₂ : Dependent₁Category D₁₁}
  → {D₂₂ : Dependent₁Category D₂₁}
  → {F₁ : Functor C₁₁ C₂₁}
  → {G₁ : Functor D₁₁ D₂₁}
  → {H₁₁ : Functor C₁₁ D₁₁}
  → {H₂₁ : Functor C₂₁ D₂₁}
  → {F₂ : Dependent₁Functor C₁₂ C₂₂ F₁}
  → {G₂ : Dependent₁Functor D₁₂ D₂₂ G₁}
  → {H₁₂ : Dependent₁Functor C₁₂ D₁₂ H₁₁}
  → {H₂₂ : Dependent₁Functor C₂₂ D₂₂ H₂₁}
  → FunctorSquare F₁ G₁ H₁₁ H₂₁
  → Dependent₁FunctorSquare F₂ G₂ H₁₂ H₂₂
  → FunctorSquare
    (functor-sigma F₂)
    (functor-sigma G₂)
    (functor-sigma H₁₂)
    (functor-sigma H₂₂)
functor-square-sigma {F₂ = F₂} {G₂ = G₂} {H₁₂ = H₁₂} {H₂₂ = H₂₂} s₁ s₂
  = functor-square-from-equal
    (functor-sigma F₂)
    (functor-sigma G₂)
    (functor-sigma H₁₂)
    (functor-sigma H₂₂)
  $ functor-trans (functor-sym
    (functor-sigma-compose H₂₂ F₂))
  $ functor-trans (functor-equal-sigma
    (functor-square-to-equal s₁)
    (dependent₁-functor-square-to-equal s₂))
  $ functor-sigma-compose G₂ H₁₂

-- ## FunctorSquare₁

functor-square-sigma₁
  : {C₁₁ C₂₁ : Category}
  → {C₁₂ : Dependent₁Category C₁₁}
  → {C₂₂ : Dependent₁Category C₂₁}
  → {F₁ : Functor C₁₁ C₂₁}
  → (F₂ : Dependent₁Functor C₁₂ C₂₂ F₁)
  → FunctorSquare
    (functor-sigma F₂) F₁
    (functor-sigma₁ C₁₂)
    (functor-sigma₁ C₂₂)
functor-square-sigma₁ {C₂₁ = C₂₁} _
  = record
  { base
    = λ _ → refl
  ; map
    = λ _ → Category.arrow-refl' C₂₁
  }
  
