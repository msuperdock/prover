module Prover.Category.Product where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare; functor-compose'; functor-compose-from-equal;
    functor-compose-to-equal; functor-identity'; functor-identity-from-equal;
    functor-identity-to-equal; functor-square-from-equal;
    functor-square-to-equal; functor-sym; functor-trans)
open import Prover.Prelude

-- ## Category

module CategoryProduct
  (C₁ : Category)
  (C₂ : Category)
  where

  Object
    : Set
  Object
    = Category.Object C₁
    × Category.Object C₂

  Arrow
    : Object
    → Object
    → Set
  Arrow (x₁ , x₂) (y₁ , y₂)
    = Category.Arrow C₁ x₁ y₁
    × Category.Arrow C₂ x₂ y₂

  identity
    : (x : Object)
    → Arrow x x
  identity (x₁ , x₂)
    = Category.identity C₁ x₁
    , Category.identity C₂ x₂

  compose
    : {x y z : Object}
    → Arrow y z
    → Arrow x y
    → Arrow x z
  compose (f₁ , f₂) (g₁ , g₂)
    = Category.compose C₁ f₁ g₁
    , Category.compose C₂ f₂ g₂

  abstract

    precompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose f (identity x) ≡ f
    precompose (f₁ , f₂)
      = Sigma.comma-eq
        (Category.precompose C₁ f₁)
        (Category.precompose C₂ f₂)
  
    postcompose
      : {x y : Object}
      → (f : Arrow x y)
      → compose (identity y) f ≡ f
    postcompose (f₁ , f₂)
      = Sigma.comma-eq
        (Category.postcompose C₁ f₁)
        (Category.postcompose C₂ f₂)
  
    associative
      : {x y z w : Object}
      → (f : Arrow z w)
      → (g : Arrow y z)
      → (h : Arrow x y)
      → compose (compose f g) h ≡ compose f (compose g h)
    associative (f₁ , f₂) (g₁ , g₂) (h₁ , h₂)
      = Sigma.comma-eq
        (Category.associative C₁ f₁ g₁ h₁)
        (Category.associative C₂ f₂ g₂ h₂)
  
category-product
  : Category
  → Category
  → Category
category-product C₁ C₂
  = record {CategoryProduct C₁ C₂}
  
-- ## Functor

-- ### Function

module _
  {C₁ C₂ D₁ D₂ : Category}
  where

  module FunctorProduct
    (F₁ : Functor C₁ D₁)
    (F₂ : Functor C₂ D₂)
    where

    base
      : Category.Object (category-product C₁ C₂)
      → Category.Object (category-product D₁ D₂)
    base (x₁ , x₂)
      = Functor.base F₁ x₁
      , Functor.base F₂ x₂

    map
      : {x y : Category.Object (category-product C₁ C₂)}
      → Category.Arrow (category-product C₁ C₂) x y
      → Category.Arrow (category-product D₁ D₂) (base x) (base y)
    map (f₁ , f₂)
      = Functor.map F₁ f₁
      , Functor.map F₂ f₂

    abstract

      map-identity
        : (x : Category.Object (category-product C₁ C₂))
        → map (Category.identity (category-product C₁ C₂) x)
          ≡ Category.identity (category-product D₁ D₂) (base x)
      map-identity (x₁ , x₂)
        = Sigma.comma-eq
          (Functor.map-identity F₁ x₁)
          (Functor.map-identity F₂ x₂)
  
      map-compose
        : {x y z : Category.Object (category-product C₁ C₂)}
        → (f : Category.Arrow (category-product C₁ C₂) y z)
        → (g : Category.Arrow (category-product C₁ C₂) x y)
        → map (Category.compose (category-product C₁ C₂) f g)
          ≡ Category.compose (category-product D₁ D₂) (map f) (map g)
      map-compose (f₁ , f₂) (g₁ , g₂)
        = Sigma.comma-eq
          (Functor.map-compose F₁ f₁ g₁)
          (Functor.map-compose F₂ f₂ g₂)

  functor-product
    : Functor C₁ D₁
    → Functor C₂ D₂
    → Functor
      (category-product C₁ C₂)
      (category-product D₁ D₂)
  functor-product F₁ F₂
    = record {FunctorProduct F₁ F₂}

-- ### Identity

module FunctorProductIdentity
  (C₁ C₂ : Category)
  where

  base
    : (x : Category.Object (category-product C₁ C₂))
    → Functor.base
      (functor-product (functor-identity' C₁) (functor-identity' C₂)) x
    ≡ Functor.base
      (functor-identity' (category-product C₁ C₂)) x
  base _
    = refl

  map
    : {x y : Category.Object (category-product C₁ C₂)}
    → (f : Category.Arrow (category-product C₁ C₂) x y)
    → Functor.map
      (functor-product (functor-identity' C₁) (functor-identity' C₂)) f
    ≅ Functor.map (functor-identity' (category-product C₁ C₂)) f
  map _
    = refl

functor-product-identity
  : (C₁ C₂ : Category)
  → FunctorEqual
    (functor-product (functor-identity' C₁) (functor-identity' C₂))
    (functor-identity' (category-product C₁ C₂))
functor-product-identity C₁ C₂
  = record {FunctorProductIdentity C₁ C₂}

-- ### Compose

module _
  {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  where

  module FunctorProductCompose
    (F₁ : Functor D₁ E₁)
    (F₂ : Functor D₂ E₂)
    (G₁ : Functor C₁ D₁)
    (G₂ : Functor C₂ D₂)
    where
  
    base
      : (x : Category.Object (category-product C₁ C₂))
      → Functor.base
        (functor-product (functor-compose' F₁ G₁) (functor-compose' F₂ G₂)) x
      ≡ Functor.base
        (functor-compose' (functor-product F₁ F₂) (functor-product G₁ G₂)) x
    base _
      = refl
  
    map
      : {x y : Category.Object (category-product C₁ C₂)}
      → (f : Category.Arrow (category-product C₁ C₂) x y)
      → Functor.map
        (functor-product (functor-compose' F₁ G₁) (functor-compose' F₂ G₂)) f
      ≅ Functor.map
        (functor-compose' (functor-product F₁ F₂) (functor-product G₁ G₂)) f
    map _
      = refl

  functor-product-compose
    : (F₁ : Functor D₁ E₁)
    → (F₂ : Functor D₂ E₂)
    → (G₁ : Functor C₁ D₁)
    → (G₂ : Functor C₂ D₂)
    → FunctorEqual
      (functor-product (functor-compose' F₁ G₁) (functor-compose' F₂ G₂))
      (functor-compose' (functor-product F₁ F₂) (functor-product G₁ G₂))
  functor-product-compose F₁ F₂ G₁ G₂
    = record {FunctorProductCompose F₁ F₂ G₁ G₂}

-- ## FunctorEqual

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F₁₁ F₂₁ : Functor C₁ D₁}
  {F₁₂ F₂₂ : Functor C₂ D₂}
  where

  module FunctorEqualProduct
    (p₁ : FunctorEqual F₁₁ F₂₁)
    (p₂ : FunctorEqual F₁₂ F₂₂)
    where

    base
      : (x : Category.Object (category-product C₁ C₂))
      → Functor.base (functor-product F₁₁ F₁₂) x
        ≅ Functor.base (functor-product F₂₁ F₂₂) x
    base (x₁ , x₂)
      with Functor.base F₁₁ x₁
      | FunctorEqual.base p₁ x₁
      | Functor.base F₁₂ x₂
      | FunctorEqual.base p₂ x₂
    ... | _ | refl | _ | refl
      = refl

    map
      : {x y : Category.Object (category-product C₁ C₂)}
      → (f : Category.Arrow (category-product C₁ C₂) x y)
      → Functor.map (functor-product F₁₁ F₁₂) f
        ≅ Functor.map (functor-product F₂₁ F₂₂) f
    map {x = (x₁ , x₂)} {y = (y₁ , y₂)} (f₁ , f₂)
      with Functor.base F₁₁ x₁
      | FunctorEqual.base p₁ x₁
      | Functor.base F₁₂ x₂
      | FunctorEqual.base p₂ x₂
      | Functor.base F₁₁ y₁
      | FunctorEqual.base p₁ y₁
      | Functor.base F₁₂ y₂
      | FunctorEqual.base p₂ y₂
      | Functor.map F₁₁ f₁
      | FunctorEqual.map p₁ f₁
      | Functor.map F₁₂ f₂
      | FunctorEqual.map p₂ f₂
    ... | _ | refl | _ | refl | _ | refl | _ | refl | _ | refl | _ | refl
      = refl

  functor-equal-product
    : FunctorEqual F₁₁ F₂₁
    → FunctorEqual F₁₂ F₂₂
    → FunctorEqual
      (functor-product F₁₁ F₁₂)
      (functor-product F₂₁ F₂₂)
  functor-equal-product p₁ p₂
    = record {FunctorEqualProduct p₁ p₂}

-- ## FunctorIdentity

functor-identity-product
  : {C₁ C₂ : Category}
  → {F₁ : Functor C₁ C₁}
  → {F₂ : Functor C₂ C₂}
  → FunctorIdentity F₁
  → FunctorIdentity F₂
  → FunctorIdentity
    (functor-product F₁ F₂)
functor-identity-product
  {C₁ = C₁} {C₂ = C₂} p₁ p₂
  = functor-identity-from-equal
  $ functor-trans (functor-equal-product
    (functor-identity-to-equal p₁)
    (functor-identity-to-equal p₂))
  $ functor-product-identity C₁ C₂

-- ## FunctorCompose

functor-compose-product
  : {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  → {F₁ : Functor D₁ E₁}
  → {F₂ : Functor D₂ E₂}
  → {G₁ : Functor C₁ D₁}
  → {G₂ : Functor C₂ D₂}
  → {H₁ : Functor C₁ E₁}
  → {H₂ : Functor C₂ E₂}
  → FunctorCompose F₁ G₁ H₁
  → FunctorCompose F₂ G₂ H₂
  → FunctorCompose
    (functor-product F₁ F₂)
    (functor-product G₁ G₂)
    (functor-product H₁ H₂)
functor-compose-product
  {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p₁ p₂
  = functor-compose-from-equal
    (functor-product F₁ F₂)
    (functor-product G₁ G₂)
  $ functor-trans (functor-equal-product
    (functor-compose-to-equal p₁)
    (functor-compose-to-equal p₂))
  $ functor-product-compose F₁ F₂ G₁ G₂

-- ## FunctorSquare

functor-square-product
  : {C₁₁ C₁₂ C₂₁ C₂₂ D₁₁ D₁₂ D₂₁ D₂₂ : Category}
  → {F₁ : Functor C₁₁ C₂₁}
  → {F₂ : Functor C₁₂ C₂₂}
  → {G₁ : Functor D₁₁ D₂₁}
  → {G₂ : Functor D₁₂ D₂₂}
  → {H₁₁ : Functor C₁₁ D₁₁}
  → {H₁₂ : Functor C₁₂ D₁₂}
  → {H₂₁ : Functor C₂₁ D₂₁}
  → {H₂₂ : Functor C₂₂ D₂₂}
  → FunctorSquare F₁ G₁ H₁₁ H₂₁
  → FunctorSquare F₂ G₂ H₁₂ H₂₂
  → FunctorSquare
    (functor-product F₁ F₂)
    (functor-product G₁ G₂)
    (functor-product H₁₁ H₁₂)
    (functor-product H₂₁ H₂₂)
functor-square-product
  {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂}
  {H₁₁ = H₁₁} {H₁₂ = H₁₂} {H₂₁ = H₂₁} {H₂₂ = H₂₂} s₁ s₂
  = functor-square-from-equal
    (functor-product F₁ F₂)
    (functor-product G₁ G₂)
    (functor-product H₁₁ H₁₂)
    (functor-product H₂₁ H₂₂)
  $ functor-trans (functor-sym
    (functor-product-compose H₂₁ H₂₂ F₁ F₂))
  $ functor-trans (functor-equal-product
    (functor-square-to-equal s₁)
    (functor-square-to-equal s₂))
  $ functor-product-compose G₁ G₂ H₁₁ H₁₂

