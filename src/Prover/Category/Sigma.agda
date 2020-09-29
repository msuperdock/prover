module Prover.Category.Sigma where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare; functor-compose'; functor-compose-from-equal;
    functor-identity'; functor-identity-from-equal; functor-square-from-equal;
    functor-sym; functor-trans)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor; Dependent₁FunctorCompose;
    Dependent₁FunctorEqual; Dependent₁FunctorIdentity; Dependent₁FunctorSquare;
    dependent₁-functor-compose; dependent₁-functor-compose-to-equal;
    dependent₁-functor-identity; dependent₁-functor-identity-to-equal;
    dependent₁-functor-square-to-equal)
open import Prover.Prelude

-- ## Category

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
  
        domain
          : Dependent₁Category.Object C₂ (π₁ y)
  
        arrow₁
          : Category.Arrow C₁ (π₁ x) (π₁ y)
  
        arrow₂
          : Dependent₁Category.Arrow C₂ (π₁ y) domain (π₂ y)
  
        valid
          : Dependent₁Category.base C₂ arrow₁ (π₂ x) ≡ domain
  
    arrow-eq
      : {x y : Object}
      → {f₁ f₂ : Arrow x y}
      → Arrow.domain f₁ ≡ Arrow.domain f₂
      → Arrow.arrow₁ f₁ ≡ Arrow.arrow₁ f₂
      → Arrow.arrow₂ f₁ ≅ Arrow.arrow₂ f₂
      → f₁ ≡ f₂
    arrow-eq {f₁ = arrow y₁₂' f₁₁ f₁₂ p₁₂} {f₂ = arrow _ _ _ p₂₂} refl refl refl
      = sub (arrow y₁₂' f₁₁ f₁₂) (irrelevant p₁₂ p₂₂)
  
    arrow-eq'
      : {x₁ x₂ y₁ y₂ : Object}
      → {f₁ : Arrow x₁ y₁}
      → {f₂ : Arrow x₂ y₂}
      → x₁ ≡ x₂
      → y₁ ≡ y₂
      → Arrow.domain f₁ ≅ Arrow.domain f₂
      → Arrow.arrow₁ f₁ ≅ Arrow.arrow₁ f₂
      → Arrow.arrow₂ f₁ ≅ Arrow.arrow₂ f₂
      → f₁ ≅ f₂
    arrow-eq' refl refl
      = arrow-eq

    identity
      : (x : Object)
      → Arrow x x
    identity (x₁ , x₂)
      = record
      { domain
        = x₂
      ; arrow₁
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
      (arrow _ f₁ f₂ p₂)
      (arrow y₂' g₁ g₂ q₂)
      = record
      { domain
        = Dependent₁Category.base C₂ f₁ y₂'
      ; arrow₁
        = Category.compose C₁ f₁ g₁
      ; arrow₂
        = Dependent₁Category.compose-eq' C₂ z₁ p₂ f₂
          (Dependent₁Category.map C₂ f₁ g₂)
      ; valid
        = trans (Dependent₁Category.base-compose C₂ f₁ g₁ x₂)
          (sub (Dependent₁Category.base C₂ f₁) q₂)
      }
  
    abstract

      precompose₂
        : {x₁ : Category.Object C₁}
        → {x₂ y₂ z₂ : Dependent₁Category.Object C₂ x₁}
        → {f₂ : Dependent₁Category.Arrow C₂ x₁ y₂ z₂}
        → {g₂ : Dependent₁Category.Arrow C₂ x₁ x₂ x₂}
        → (p₂ : x₂ ≡ y₂)
        → (g₂ ≡ Dependent₁Category.identity C₂ x₁ x₂)
        → Dependent₁Category.compose-eq' C₂ x₁ p₂ f₂ g₂ ≅ f₂
      precompose₂ {x₁ = x₁} {f₂ = f₂} refl refl
        = Dependent₁Category.precompose C₂ x₁ f₂
    
      precompose
        : {x y : Object}
        → (f : Arrow x y)
        → compose f (identity x) ≡ f
      precompose {x = (_ , x₂)} (arrow _ f₁ _ p₂)
        = arrow-eq p₂
          (Category.precompose C₁ f₁)
          (precompose₂ p₂ (Dependent₁Category.map-identity' C₂ f₁ x₂))
    
      postcompose₂
        : {x₁ : Category.Object C₁}
        → {w₂ x₂ y₂ z₂ : Dependent₁Category.Object C₂ x₁}
        → {g₂ : Dependent₁Category.Arrow C₂ x₁ w₂ y₂}
        → {h₂ : Dependent₁Category.Arrow C₂ x₁ x₂ z₂}
        → (p₂ : y₂ ≡ z₂)
        → (w₂ ≡ x₂)
        → g₂ ≅ h₂
        → Dependent₁Category.compose-eq' C₂ x₁ p₂
          (Dependent₁Category.identity C₂ x₁ z₂) g₂
        ≅ h₂
      postcompose₂ {x₁ = x₁} {g₂ = g₂} refl refl refl 
        = Dependent₁Category.postcompose C₂ x₁ g₂
    
      postcompose
        : {x y : Object}
        → (f : Arrow x y)
        → compose (identity y) f ≡ f
      postcompose {y = (y₁ , y₂)} (arrow y₂' f₁ f₂ _)
        = arrow-eq
          (Dependent₁Category.base-identity C₂ y₁ y₂')
          (Category.postcompose C₁ f₁)
          (postcompose₂
            (Dependent₁Category.base-identity C₂ y₁ y₂)
            (Dependent₁Category.base-identity C₂ y₁ y₂')
            (Dependent₁Category.map-identity C₂ y₁ f₂))
    
      associative₂
        : {x₁ : Category.Object C₁}
        → {u₂ u₂' v₂ v₂' w₂ x₂ y₂ z₂ : Dependent₁Category.Object C₂ x₁}
        → {h₂ : Dependent₁Category.Arrow C₂ x₁ u₂ v₂}
        → {h₂' : Dependent₁Category.Arrow C₂ x₁ u₂' v₂'}
        → (f₂ : Dependent₁Category.Arrow C₂ x₁ y₂ z₂)
        → (g₂ : Dependent₁Category.Arrow C₂ x₁ w₂ x₂)
        → (p₂ : v₂ ≡ w₂)
        → (q₂ : x₂ ≡ y₂)
        → (r₂ : v₂' ≡ w₂)
        → u₂ ≡ u₂'
        → h₂ ≅ h₂'
        → Dependent₁Category.compose-eq' C₂ x₁ p₂
          (Dependent₁Category.compose-eq' C₂ x₁ q₂ f₂ g₂) h₂
        ≅ Dependent₁Category.compose-eq' C₂ x₁ q₂ f₂
          (Dependent₁Category.compose-eq' C₂ x₁ r₂ g₂ h₂')
      associative₂ {x₁ = x₁} {h₂ = h₂} f₂ g₂ refl refl refl refl refl
        = Dependent₁Category.associative C₂ x₁ f₂ g₂ h₂
    
      associative₂'
        : {x₁ y₁ z₁ : Category.Object C₁}
        → {x₂ x₂' : Dependent₁Category.Object C₂ x₁}
        → {y₂ y₂' : Dependent₁Category.Object C₂ y₁}
        → {z₂ z₂' : Dependent₁Category.Object C₂ z₁}
        → (f₁ : Category.Arrow C₁ y₁ z₁)
        → (f₂ : Dependent₁Category.Arrow C₂ z₁ z₂' z₂)
        → (g₁ : Category.Arrow C₁ x₁ y₁)
        → (g₂ : Dependent₁Category.Arrow C₂ y₁ y₂' y₂)
        → (h₂ : Dependent₁Category.Arrow C₂ x₁ x₂' x₂)
        → (p₂ : Dependent₁Category.base C₂ (Category.compose C₁ f₁ g₁) x₂
          ≡ Dependent₁Category.base C₂ f₁ y₂')
        → (q₂ : Dependent₁Category.base C₂ f₁ y₂ ≡ z₂')
        → (r₂ : Dependent₁Category.base C₂ g₁ x₂ ≡ y₂')
        → Dependent₁Category.compose-eq' C₂ z₁ p₂
          (Dependent₁Category.compose-eq' C₂ z₁ q₂ f₂
            (Dependent₁Category.map C₂ f₁ g₂))
          (Dependent₁Category.map C₂ (Category.compose C₁ f₁ g₁) h₂)
        ≅ Dependent₁Category.compose-eq' C₂ z₁ q₂ f₂
          (Dependent₁Category.map C₂ f₁
            (Dependent₁Category.compose-eq' C₂ y₁ r₂ g₂
              (Dependent₁Category.map C₂ g₁ h₂)))
      associative₂' {y₁ = y₁} {x₂' = x₂'} f₁ f₂ g₁ g₂ h₂ p₂ q₂ r₂
        with Dependent₁Category.map C₂ f₁
          (Dependent₁Category.compose-eq' C₂ y₁ r₂ g₂
            (Dependent₁Category.map C₂ g₁ h₂))
        | Dependent₁Category.map-compose-eq C₂ f₁ r₂
          (sub (Dependent₁Category.base C₂ f₁) r₂) g₂
          (Dependent₁Category.map C₂ g₁ h₂)
      ... | _ | refl
        = associative₂ f₂ 
          (Dependent₁Category.map C₂ f₁ g₂) p₂ q₂
          (sub (Dependent₁Category.base C₂ f₁) r₂)
          (Dependent₁Category.base-compose C₂ f₁ g₁ x₂')
          (Dependent₁Category.map-compose C₂ f₁ g₁ h₂)
    
      associative
        : {w x y z : Object}
        → (f : Arrow y z)
        → (g : Arrow x y)
        → (h : Arrow w x)
        → compose (compose f g) h ≡ compose f (compose g h)
      associative {x = (_ , x₂)}
        (arrow _ f₁ f₂ p₂)
        (arrow _ g₁ g₂ q₂)
        (arrow x₂' h₁ h₂ _)
        = arrow-eq
          (Dependent₁Category.base-compose C₂ f₁ g₁ x₂')
          (Category.associative C₁ f₁ g₁ h₁)
          (associative₂' f₁ f₂ g₁ g₂ h₂
            (trans (Dependent₁Category.base-compose C₂ f₁ g₁ x₂)
              (sub (Dependent₁Category.base C₂ f₁) q₂)) p₂ q₂)

  category-sigma
    : Dependent₁Category C₁
    → Category
  category-sigma C₂
    = record {CategorySigma C₂}

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
    map {x = (_ , x₂)} {y = (y₁ , _)} (CategorySigma.arrow y₂' f₁ f₂ p₂)
      = record
      { domain
        = Dependent₁Functor.base F₂ y₁ y₂'
      ; arrow₁
        = Functor.map F₁ f₁
      ; arrow₂
        = Dependent₁Functor.map F₂ y₁ f₂
      ; valid
        = trans
          (sym (Dependent₁Functor.base-square F₂ f₁ x₂))
          (sub (Dependent₁Functor.base F₂ y₁) p₂)
      }

    abstract

      map-identity
        : (x : Category.Object (category-sigma C₂))
        → map (Category.identity (category-sigma C₂) x)
          ≡ Category.identity (category-sigma D₂) (base x)
      map-identity (x₁ , x₂)
        = CategorySigma.arrow-eq D₂ refl
          (Functor.map-identity F₁ x₁)
          (Dependent₁Functor.map-identity F₂ x₁ x₂)
  
      map-compose₂
        : (z₁' : Category.Object D₁)
        → {w₂' w₂'' x₂' x₂'' y₂' z₂' : Dependent₁Category.Object D₂ z₁'}
        → {g₂' : Dependent₁Category.Arrow D₂ z₁' w₂' x₂'}
        → {g₂'' : Dependent₁Category.Arrow D₂ z₁' w₂'' x₂''}
        → (p₂' : x₂' ≡ y₂')
        → (p₂'' : x₂'' ≡ y₂')
        → (f₂' : Dependent₁Category.Arrow D₂ z₁' y₂' z₂')
        → w₂' ≡ w₂''
        → x₂' ≡ x₂''
        → g₂' ≅ g₂''
        → Dependent₁Category.compose-eq' D₂ z₁' p₂' f₂' g₂'
          ≅ Dependent₁Category.compose-eq' D₂ z₁' p₂'' f₂' g₂''
      map-compose₂ _ refl refl _ refl refl refl
        = refl
  
      map-compose
        : {x y z : Category.Object (category-sigma C₂)}
        → (f : Category.Arrow (category-sigma C₂) y z)
        → (g : Category.Arrow (category-sigma C₂) x y)
        → map (Category.compose (category-sigma C₂) f g)
          ≡ Category.compose (category-sigma D₂) (map f) (map g)
      map-compose {y = (_ , y₂)} {z = (z₁ , _)}
        (CategorySigma.arrow _ f₁ f₂ p₂)
        (CategorySigma.arrow y₂' g₁ g₂ _)
        = CategorySigma.arrow-eq D₂
          (Dependent₁Functor.base-square F₂ f₁ y₂')
          (Functor.map-compose F₁ f₁ g₁)
        $ trans (Dependent₁Functor.map-compose-eq F₂ z₁ p₂
          (sub (Dependent₁Functor.base F₂ z₁) p₂) f₂
            (Dependent₁Category.map C₂ f₁ g₂))
        $ map-compose₂
          (Functor.base F₁ z₁)
          (sub (Dependent₁Functor.base F₂ z₁) p₂)
          (trans (sym (Dependent₁Functor.base-square F₂ f₁ y₂))
            (sub (Dependent₁Functor.base F₂ z₁) p₂))
          (Dependent₁Functor.map F₂ z₁ f₂)
          (Dependent₁Functor.base-square F₂ f₁ y₂')
          (Dependent₁Functor.base-square F₂ f₁ y₂)
          (Dependent₁Functor.map-square F₂ f₁ g₂)

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
      → Functor.map (functor-sigma (dependent₁-functor-identity C₂)) f
        ≅ Functor.map (functor-identity' (category-sigma C₂)) f
    map _
      = CategorySigma.arrow-eq C₂ refl refl refl

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
      → Functor.map
        (functor-sigma (dependent₁-functor-compose F₂ G₂)) f
      ≅ Functor.map
        (functor-compose' (functor-sigma F₂) (functor-sigma G₂)) f
    map _
      = CategorySigma.arrow-eq E₂ refl refl refl

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
    base
      = π₁

    map
      : {x₁ y₁ : Category.Object (category-sigma C₂)}
      → Category.Arrow (category-sigma C₂) x₁ y₁
      → Category.Arrow C₁ (base x₁) (base y₁)
    map
      = CategorySigma.Arrow.arrow₁

    abstract

      map-identity
        : (x₁ : Category.Object (category-sigma C₂))
        → map (Category.identity (category-sigma C₂) x₁)
          ≡ Category.identity C₁ (base x₁)
      map-identity _
        = refl
  
      map-compose
        : {x₁ y₁ z₁ : Category.Object (category-sigma C₂)}
        → (f₁ : Category.Arrow (category-sigma C₂) y₁ z₁)
        → (g₁ : Category.Arrow (category-sigma C₂) x₁ y₁)
        → map (Category.compose (category-sigma C₂) f₁ g₁)
          ≡ Category.compose C₁ (map f₁) (map g₁)
      map-compose _ _
        = refl
  
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
  {F₁ F₂ : Functor C₁ D₁}
  {F₁₂ : Dependent₁Functor C₂ D₂ F₁}
  {F₂₂ : Dependent₁Functor C₂ D₂ F₂}
  where
  
  module FunctorEqualSigma
    (p : Dependent₁FunctorEqual F₁₂ F₂₂)
    where

    base
      : (x : Category.Object (category-sigma C₂))
      → Functor.base (functor-sigma F₁₂) x ≅ Functor.base (functor-sigma F₂₂) x
    base (x₁ , x₂)
      = Sigma.comma-eq
        (Dependent₁FunctorEqual.base p x₁)
        (Dependent₁FunctorEqual.base' p x₁ x₂)
  
    map
      : {x y : Category.Object (category-sigma C₂)}
      → (f : Category.Arrow (category-sigma C₂) x y)
      → Functor.map (functor-sigma F₁₂) f ≅ Functor.map (functor-sigma F₂₂) f
    map {x = x} {y = y@(y₁ , _)} (CategorySigma.arrow y₂' f₁ f₂ _)
      = CategorySigma.arrow-eq' D₂ (base x) (base y)
        (Dependent₁FunctorEqual.base' p y₁ y₂')
        (Dependent₁FunctorEqual.map p f₁)
        (Dependent₁FunctorEqual.map' p y₁ f₂)

  functor-equal-sigma
    : Dependent₁FunctorEqual F₁₂ F₂₂
    → FunctorEqual
      (functor-sigma F₁₂)
      (functor-sigma F₂₂)
  functor-equal-sigma p
    = record {FunctorEqualSigma p}

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
    (dependent₁-functor-identity-to-equal p₁ p₂))
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
    (dependent₁-functor-compose-to-equal p₁ p₂))
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
    (dependent₁-functor-square-to-equal s₁ s₂))
  $ functor-sigma-compose G₂ H₁₂

-- ## FunctorSquare₁

module _
  {C₁₁ C₂₁ : Category}
  {C₁₂ : Dependent₁Category C₁₁}
  {C₂₂ : Dependent₁Category C₂₁}
  {F₁ : Functor C₁₁ C₂₁}
  where

  module FunctorSquareSigma₁
    (F₂ : Dependent₁Functor C₁₂ C₂₂ F₁)
    where

    base
      : (x₁ : Category.Object (category-sigma C₁₂))
      → Functor.base (functor-sigma₁ C₂₂) (Functor.base (functor-sigma F₂) x₁) 
      ≅ Functor.base F₁ (Functor.base (functor-sigma₁ C₁₂) x₁)
    base _
      = refl
  
    map
      : {x₁ y₁ : Category.Object (category-sigma C₁₂)}
      → (f₁ : Category.Arrow (category-sigma C₁₂) x₁ y₁)
      → Functor.map (functor-sigma₁ C₂₂) (Functor.map (functor-sigma F₂) f₁)
      ≅ Functor.map F₁ (Functor.map (functor-sigma₁ C₁₂) f₁)
    map _
      = refl

  functor-square-sigma₁
    : (F₂ : Dependent₁Functor C₁₂ C₂₂ F₁)
    → FunctorSquare
      (functor-sigma F₂) F₁
      (functor-sigma₁ C₁₂)
      (functor-sigma₁ C₂₂)
  functor-square-sigma₁ F₂
    = record {FunctorSquareSigma₁ F₂}
  
