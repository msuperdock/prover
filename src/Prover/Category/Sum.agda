module Prover.Category.Sum where

open import Prover.Category
  using (module Category'; Category; Functor; FunctorCompose; FunctorEqual;
    FunctorIdentity; FunctorSquare; any; any'; functor-compose';
    functor-compose-from-equal; functor-compose-to-equal; functor-identity';
    functor-identity-from-equal; functor-identity-to-equal;
    functor-square-compose'; functor-square-identity';
    functor-square-from-equal; functor-square-to-equal; functor-sym;
    functor-trans)
open import Prover.Prelude

-- ## Category

-- ### Function

module _
  {C₁ C₂ : Category}
  where
  
  module CategorySum
    (F : Functor C₂ C₁)
    where

    Object
      : Set
    Object
      = Category.Object C₁
      ⊔ Category.Object C₂

    object₁
      : Object
      → Category.Object C₁
    object₁ (ι₁ x₁)
      = x₁
    object₁ (ι₂ x₂)
      = Functor.base F x₂

    data Arrow
      : Object
      → Object
      → Set
      where

      arrow₁
        : {x y : Object}
        → Category.Arrow C₁ (object₁ x) (object₁ y)
        → Arrow x y

      arrow₂
        : {x₂ y₂ : Category.Object C₂}
        → Category.Arrow C₂ x₂ y₂
        → Arrow (ι₂ x₂) (ι₂ y₂)

    data ArrowEqual
      : {x y : Object}
      → Arrow x y
      → Arrow x y
      → Set
      where

      arrow₁-equal
        : {x y : Object}
        → {f₁₁ f₁₂ : Category.Arrow C₁ (object₁ x) (object₁ y)}
        → Category.ArrowEqual C₁ f₁₁ f₁₂
        → ArrowEqual {x = x} {y = y} (arrow₁ f₁₁) (arrow₁ f₁₂)

      arrow₂-equal
        : {x₂ y₂ : Category.Object C₂}
        → {f₂₁ f₂₂ : Category.Arrow C₂ x₂ y₂}
        → Category.ArrowEqual C₂ f₂₁ f₂₂
        → ArrowEqual (arrow₂ f₂₁) (arrow₂ f₂₂)

    abstract

      arrow-refl
        : {x y : Object}
        → {f : Arrow x y}
        → ArrowEqual f f
      arrow-refl {f = arrow₁ _}
        = arrow₁-equal
        $ Category.arrow-refl C₁
      arrow-refl {f = arrow₂ _}
        = arrow₂-equal
        $ Category.arrow-refl C₂

      arrow-sym
        : {x y : Object}
        → {f₁ f₂ : Arrow x y}
        → ArrowEqual f₁ f₂
        → ArrowEqual f₂ f₁
      arrow-sym (arrow₁-equal p₁)
        = arrow₁-equal
        $ Category.arrow-sym C₁ p₁
      arrow-sym (arrow₂-equal p₂)
        = arrow₂-equal
        $ Category.arrow-sym C₂ p₂

      arrow-trans
        : {x y : Object}
        → {f₁ f₂ f₃ : Arrow x y}
        → ArrowEqual f₁ f₂
        → ArrowEqual f₂ f₃
        → ArrowEqual f₁ f₃
      arrow-trans (arrow₁-equal p₁₁) (arrow₁-equal p₁₂)
        = arrow₁-equal
        $ Category.arrow-trans C₁ p₁₁ p₁₂
      arrow-trans (arrow₂-equal p₂₁) (arrow₂-equal p₂₂)
        = arrow₂-equal
        $ Category.arrow-trans C₂ p₂₁ p₂₂

      simplify
        : {x y : Object}
        → Arrow x y
        → Arrow x y
      simplify (arrow₁ f₁)
        = arrow₁
        $ Category.simplify C₁ f₁
      simplify (arrow₂ f₂)
        = arrow₂
        $ Category.simplify C₂ f₂

      simplify-equal
        : {x y : Object}
        → (f : Arrow x y)
        → ArrowEqual
          (simplify f) f
      simplify-equal (arrow₁ f₁)
        = arrow₁-equal
        $ Category.simplify-equal C₁ f₁
      simplify-equal (arrow₂ f₂)
        = arrow₂-equal
        $ Category.simplify-equal C₂ f₂

    identity
      : (x : Object)
      → Arrow x x
    identity (ι₁ x₁)
      = arrow₁
      $ Category.identity C₁ x₁
    identity (ι₂ x₂)
      = arrow₂
      $ Category.identity C₂ x₂

    compose
      : {x y z : Object}
      → Arrow y z
      → Arrow x y
      → Arrow x z
    compose (arrow₁ f₁) (arrow₁ g₁)
      = arrow₁
      $ Category.compose C₁ f₁ g₁
    compose (arrow₁ f₁) (arrow₂ g₂)
      = arrow₁
      $ Category.compose C₁ f₁ (Functor.map F g₂)
    compose (arrow₂ f₂) (arrow₁ g₁)
      = arrow₁
      $ Category.compose C₁ (Functor.map F f₂) g₁
    compose (arrow₂ f₂) (arrow₂ g₂)
      = arrow₂
      $ Category.compose C₂ f₂ g₂

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
      compose-equal (arrow₁-equal p₁) (arrow₁-equal q₁)
        = arrow₁-equal
        $ Category.compose-equal C₁ p₁ q₁
      compose-equal (arrow₁-equal p₁) (arrow₂-equal q₂)
        = arrow₁-equal
        $ Category.compose-equal C₁ p₁ (Functor.map-equal F q₂)
      compose-equal (arrow₂-equal p₂) (arrow₁-equal q₁)
        = arrow₁-equal
        $ Category.compose-equal C₁ (Functor.map-equal F p₂) q₁
      compose-equal (arrow₂-equal p₂) (arrow₂-equal q₂)
        = arrow₂-equal
        $ Category.compose-equal C₂ p₂ q₂

      precompose
        : {x y : Object}
        → (f : Arrow x y)
        → ArrowEqual
          (compose f (identity x)) f
      precompose {x = ι₁ _} (arrow₁ f₁)
        = arrow₁-equal
        $ Category.precompose C₁ f₁
      precompose {x = ι₂ x₂} (arrow₁ f₁)
        = arrow₁-equal
        $ Category.arrow-trans C₁ (Category.compose-equal C₁
          (Category.arrow-refl C₁)
          (Functor.map-identity F x₂))
        $ Category.precompose C₁ f₁
      precompose (arrow₂ f₂)
        = arrow₂-equal
        $ Category.precompose C₂ f₂

      postcompose
        : {x y : Object}
        → (f : Arrow x y)
        → ArrowEqual
          (compose (identity y) f) f
      postcompose {y = ι₁ _} (arrow₁ f₁)
        = arrow₁-equal
        $ Category.postcompose C₁ f₁
      postcompose {y = ι₂ y₂} (arrow₁ f₁)
        = arrow₁-equal
        $ Category.arrow-trans C₁ (Category.compose-equal C₁
          (Functor.map-identity F y₂)
          (Category.arrow-refl C₁))
        $ Category.postcompose C₁ f₁
      postcompose (arrow₂ f₂)
        = arrow₂-equal
        $ Category.postcompose C₂ f₂

      associative
        : {w x y z : Object}
        → (f : Arrow y z)
        → (g : Arrow x y)
        → (h : Arrow w x)
        → ArrowEqual
          (compose (compose f g) h)
          (compose f (compose g h))
      associative (arrow₁ f₁) (arrow₁ g₁) (arrow₁ h₁)
        = arrow₁-equal
        $ Category.associative C₁ f₁ g₁ h₁
      associative (arrow₁ f₁) (arrow₁ g₁) (arrow₂ h₂)
        = arrow₁-equal
        $ Category.associative C₁ f₁ g₁
          (Functor.map F h₂)
      associative (arrow₁ f₁) (arrow₂ g₂) (arrow₁ h₁)
        = arrow₁-equal
        $ Category.associative C₁ f₁
          (Functor.map F g₂) h₁
      associative (arrow₁ f₁) (arrow₂ g₂) (arrow₂ h₂)
        = arrow₁-equal
        $ Category.arrow-trans C₁ (Category.associative C₁ f₁
          (Functor.map F g₂)
          (Functor.map F h₂))
        $ Category.arrow-sym C₁ (Category.compose-equal C₁
          (Category.arrow-refl C₁)
          (Functor.map-compose F g₂ h₂))
      associative (arrow₂ f₂) (arrow₁ g₁) (arrow₁ h₁)
        = arrow₁-equal
        $ Category.associative C₁
          (Functor.map F f₂) g₁ h₁
      associative (arrow₂ f₂) (arrow₁ g₁) (arrow₂ h₂)
        = arrow₁-equal
        $ Category.associative C₁
          (Functor.map F f₂) g₁
          (Functor.map F h₂)
      associative (arrow₂ f₂) (arrow₂ g₂) (arrow₁ h₁)
        = arrow₁-equal
        $ Category.arrow-trans C₁ (Category.compose-equal C₁
          (Functor.map-compose F f₂ g₂)
          (Category.arrow-refl C₁))
        $ Category.associative C₁
          (Functor.map F f₂)
          (Functor.map F g₂) h₁
      associative (arrow₂ f₂) (arrow₂ g₂) (arrow₂ h₂)
        = arrow₂-equal
        $ Category.associative C₂ f₂ g₂ h₂

  category-sum
    : Functor C₂ C₁
    → Category
  category-sum F
    = record {CategorySum F}

-- ### Equality

arrow-equal₁
  : {C₁ C₂ : Category}
  → (F : Functor C₂ C₁)
  → {x₁ x₂ y₁ y₂ : Category.Object (category-sum F)}
  → {f₁ : Category.Arrow C₁
    (CategorySum.object₁ F x₁)
    (CategorySum.object₁ F y₁)}
  → {f₂ : Category.Arrow C₁
    (CategorySum.object₁ F x₂)
    (CategorySum.object₁ F y₂)}
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → Category.ArrowEqual' C₁ f₁ f₂
  → Category.ArrowEqual'
    (category-sum F)
    (CategorySum.arrow₁ {x = x₁} {y = y₁} f₁)
    (CategorySum.arrow₁ {x = x₂} {y = y₂} f₂)
arrow-equal₁ _ refl refl (any p₁)
  = any (CategorySum.arrow₁-equal p₁)

arrow-equal₂
  : {C₁ C₂ : Category}
  → (F : Functor C₂ C₁)
  → {x₂₁ x₂₂ y₂₁ y₂₂ : Category.Object C₂}
  → {f₂₁ : Category.Arrow C₂ x₂₁ y₂₁}
  → {f₂₂ : Category.Arrow C₂ x₂₂ y₂₂}
  → Category.ArrowEqual' C₂ f₂₁ f₂₂
  → Category.ArrowEqual'
    (category-sum F)
    (CategorySum.arrow₂ f₂₁)
    (CategorySum.arrow₂ f₂₂)
arrow-equal₂ _ (any p)
  = any (CategorySum.arrow₂-equal p)

-- ## Functor

-- ### Function

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₂ C₁}
  {G : Functor D₂ D₁}
  {H₁ : Functor C₁ D₁}
  {H₂ : Functor C₂ D₂}
  where

  module FunctorSum
    (s : FunctorSquare H₂ H₁ F G)
    where

    base
      : Category.Object (category-sum F)
      → Category.Object (category-sum G)
    base (ι₁ x₁)
      = ι₁ (Functor.base H₁ x₁)
    base (ι₂ x₂)
      = ι₂ (Functor.base H₂ x₂)

    base-equal
      : (x : Category.Object (category-sum F))
      → CategorySum.object₁ G (base x)
        ≡ Functor.base H₁ (CategorySum.object₁ F x)
    base-equal (ι₁ _)
      = refl
    base-equal (ι₂ x₂)
      = FunctorSquare.base s x₂

    map
      : {x y : Category.Object (category-sum F)}
      → Category.Arrow (category-sum F) x y
      → Category.Arrow (category-sum G) (base x) (base y)
    map {x = x} {y = y} (CategorySum.arrow₁ f₁)
      = CategorySum.arrow₁
      $ Category.arrow D₁ (base-equal x) (base-equal y)
      $ Functor.map H₁ f₁
    map (CategorySum.arrow₂ f₂)
      = CategorySum.arrow₂
      $ Functor.map H₂ f₂

    map-equal
      : {x y : Category.Object (category-sum F)}
      → {f₁ f₂ : Category.Arrow (category-sum F) x y}
      → Category.ArrowEqual (category-sum F) f₁ f₂
      → Category.ArrowEqual (category-sum G) (map f₁) (map f₂)
    map-equal {x = x} {y = y} (CategorySum.arrow₁-equal p₁)
      = CategorySum.arrow₁-equal
      $ Category.arrow-equal D₁ (base-equal x) (base-equal y)
      $ Functor.map-equal H₁ p₁
    map-equal (CategorySum.arrow₂-equal p₂)
      = CategorySum.arrow₂-equal
      $ Functor.map-equal H₂ p₂

    map-identity
      : (x : Category.Object (category-sum F))
      → Category.ArrowEqual (category-sum G)
        (map (Category.identity (category-sum F) x))
        (Category.identity (category-sum G) (base x))
    map-identity (ι₁ x₁)
      = CategorySum.arrow₁-equal
      $ Functor.map-identity H₁ x₁
    map-identity (ι₂ x₂)
      = CategorySum.arrow₂-equal
      $ Functor.map-identity H₂ x₂

    map-arrow'
      : {x₁ y₁ : Category.Object D₁}
      → {x₂ y₂ : Category.Object C₂}
      → {f₁ : Category.Arrow D₁ x₁ y₁}
      → {f₂ : Category.Arrow C₂ x₂ y₂}
      → (p : Functor.base G (Functor.base H₂ x₂) ≡ x₁)
      → (q : Functor.base G (Functor.base H₂ y₂) ≡ y₁)
      → Category.ArrowEqual' D₁ (Functor.map H₁ (Functor.map F f₂)) f₁
      → Category.ArrowEqual D₁
        (Functor.map G (Functor.map H₂ f₂))
        (Category.arrow D₁ p q f₁)
    map-arrow' {f₂ = f₂} refl refl r
      = any' (Category.arrow-trans' D₁ (FunctorSquare.map s f₂) r)

    map-arrow
      : {x₂ y₂ : Category.Object C₂}
      → (f₂ : Category.Arrow C₂ x₂ y₂)
      → Category.ArrowEqual D₁
        (Functor.map G (Functor.map H₂ f₂))
        (Category.arrow D₁ (FunctorSquare.base s x₂) (FunctorSquare.base s y₂)
          (Functor.map H₁ (Functor.map F f₂)))
    map-arrow {x₂ = x₂} {y₂ = y₂} _
      = map-arrow' (FunctorSquare.base s x₂) (FunctorSquare.base s y₂)
      $ Category.arrow-refl' D₁

    map-compose
      : {x y z : Category.Object (category-sum F)}
      → (f : Category.Arrow (category-sum F) y z)
      → (g : Category.Arrow (category-sum F) x y)
      → Category.ArrowEqual (category-sum G)
        (map (Category.compose (category-sum F) f g))
        (Category.compose (category-sum G) (map f) (map g))

    map-compose {x = x} {y = y} {z = z}
      (CategorySum.arrow₁ f₁)
      (CategorySum.arrow₁ g₁)
      = CategorySum.arrow₁-equal
      $ Category.arrow-trans D₁ (Category.arrow-equal D₁ p r
        (Functor.map-compose H₁ f₁ g₁))
      $ Category.arrow-compose D₁ p q r
        (Functor.map H₁ f₁) (Functor.map H₁ g₁)
      where
        p = base-equal x
        q = base-equal y
        r = base-equal z

    map-compose {x = x} {y = y} {z = z}
      (CategorySum.arrow₁ f₁)
      (CategorySum.arrow₂ g₂)
      = CategorySum.arrow₁-equal
      $ Category.arrow-trans D₁ (Category.arrow-equal D₁ p r
        (Functor.map-compose H₁ f₁ (Functor.map F g₂)))
      $ Category.arrow-trans D₁ (Category.arrow-compose D₁ p q r
        (Functor.map H₁ f₁) (Functor.map H₁ (Functor.map F g₂)))
      $ Category.arrow-sym D₁ (Category.compose-equal D₁
        (Category.arrow-refl D₁) (map-arrow g₂))
      where
        p = base-equal x
        q = base-equal y
        r = base-equal z

    map-compose {x = x} {y = y} {z = z}
      (CategorySum.arrow₂ f₂)
      (CategorySum.arrow₁ g₁)
      = CategorySum.arrow₁-equal
      $ Category.arrow-trans D₁ (Category.arrow-equal D₁ p r
        (Functor.map-compose H₁ (Functor.map F f₂) g₁))
      $ Category.arrow-trans D₁ (Category.arrow-compose D₁ p q r
        (Functor.map H₁ (Functor.map F f₂)) (Functor.map H₁ g₁))
      $ Category.arrow-sym D₁ (Category.compose-equal D₁
        (map-arrow f₂) (Category.arrow-refl D₁))
      where
        p = base-equal x
        q = base-equal y
        r = base-equal z

    map-compose
      (CategorySum.arrow₂ f₂)
      (CategorySum.arrow₂ g₂)
      = CategorySum.arrow₂-equal
      $ Functor.map-compose H₂ f₂ g₂

  functor-sum
    : FunctorSquare H₂ H₁ F G
    → Functor
      (category-sum F)
      (category-sum G)
  functor-sum s
    = record {FunctorSum s}

-- ### Identity

module _
  {C₁ C₂ : Category}
  where

  module FunctorSumIdentity
    (F : Functor C₂ C₁)
    where

    base
      : (x : Category.Object (category-sum F))
      → Functor.base (functor-sum (functor-square-identity' F)) x
        ≅ Functor.base (functor-identity' (category-sum F)) x
    base (ι₁ _)
      = refl
    base (ι₂ _)
      = refl

    map
      : {x y : Category.Object (category-sum F)}
      → (f : Category.Arrow (category-sum F) x y)
      → Category'.ArrowEqual'
        (category-sum F)
        (category-sum F)
        (Functor.map (functor-sum (functor-square-identity' F)) f)
        (Functor.map (functor-identity' (category-sum F)) f)
    map {x = ι₁ _} {y = ι₁ _} (CategorySum.arrow₁ _)
      = Category.arrow-refl' (category-sum F)
    map {x = ι₁ _} {y = ι₂ _} (CategorySum.arrow₁ _)
      = Category.arrow-refl' (category-sum F)
    map {x = ι₂ _} {y = ι₁ _} (CategorySum.arrow₁ _)
      = Category.arrow-refl' (category-sum F)
    map {x = ι₂ _} {y = ι₂ _} (CategorySum.arrow₁ _)
      = Category.arrow-refl' (category-sum F)
    map (CategorySum.arrow₂ _)
      = Category.arrow-refl' (category-sum F)

  functor-sum-identity
    : (F : Functor C₂ C₁)
    → FunctorEqual
      (functor-sum (functor-square-identity' F))
      (functor-identity' (category-sum F))
  functor-sum-identity F
    = record {FunctorSumIdentity F}

-- ### Compose

module _
  {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  {F : Functor C₂ C₁}
  {G : Functor D₂ D₁}
  {H : Functor E₂ E₁}
  {I₁ : Functor D₁ E₁}
  {I₂ : Functor D₂ E₂}
  {J₁ : Functor C₁ D₁}
  {J₂ : Functor C₂ D₂}
  where

  module FunctorSumCompose
    (s : FunctorSquare I₂ I₁ G H)
    (t : FunctorSquare J₂ J₁ F G)
    where

    base
      : (x : Category.Object (category-sum F))
      → Functor.base (functor-sum (functor-square-compose' s t)) x
        ≅ Functor.base (functor-compose' (functor-sum s) (functor-sum t)) x
    base (ι₁ _)
      = refl
    base (ι₂ _)
      = refl
  
    map
      : {x y : Category.Object (category-sum F)}
      → (f : Category.Arrow (category-sum F) x y)
      → Category'.ArrowEqual'
        (category-sum H)
        (category-sum H)
        (Functor.map (functor-sum (functor-square-compose' s t)) f)
        (Functor.map (functor-compose' (functor-sum s) (functor-sum t)) f)
    map {x = x} {y = y} (CategorySum.arrow₁ f₁)
      = arrow-equal₁ H (base x) (base y)
      $ Category.arrow-trans' E₁ (Category.arrow-equal' E₁
        (FunctorSum.base-equal (functor-square-compose' s t) x)
        (FunctorSum.base-equal (functor-square-compose' s t) y)
        (Functor.map I₁ f₁'))
      $ Category.arrow-trans' E₁ (Functor.map-equal' I₁
        (Category.arrow-sym' D₁ (Category.arrow-equal' D₁ p q f₁')))
      $ Category.arrow-sym' E₁ (Category.arrow-equal' E₁
        (FunctorSum.base-equal s (Functor.base (functor-sum t) x))
        (FunctorSum.base-equal s (Functor.base (functor-sum t) y))
        (Functor.map I₁ (Category.arrow D₁ p q f₁')))
      where
        p = FunctorSum.base-equal t x
        q = FunctorSum.base-equal t y
        f₁' = Functor.map J₁ f₁

    map (CategorySum.arrow₂ _)
      = Category.arrow-refl' (category-sum H)

  functor-sum-compose
    : (s : FunctorSquare I₂ I₁ G H)
    → (t : FunctorSquare J₂ J₁ F G)
    → FunctorEqual
      (functor-sum (functor-square-compose' s t))
      (functor-compose' (functor-sum s) (functor-sum t))
  functor-sum-compose s t
    = record {FunctorSumCompose s t}

-- ## Functor₂

module _
  {C₁ C₂ : Category}
  where

  module FunctorSum₂
    (F : Functor C₂ C₁)
    where

    base
      : Category.Object C₂
      → Category.Object (category-sum F)
    base
      = ι₂

    map
      : {x₂ y₂ : Category.Object C₂}
      → Category.Arrow C₂ x₂ y₂
      → Category.Arrow (category-sum F) (base x₂) (base y₂)
    map
      = CategorySum.arrow₂

    abstract

      map-equal
        : {x₂ y₂ : Category.Object C₂}
        → {f₁₂ f₂₂ : Category.Arrow C₂ x₂ y₂}
        → Category.ArrowEqual C₂ f₁₂ f₂₂
        → Category.ArrowEqual (category-sum F) (map f₁₂) (map f₂₂)
      map-equal
        = CategorySum.arrow₂-equal

      map-identity
        : (x₂ : Category.Object C₂)
        → Category.ArrowEqual (category-sum F)
          (map (Category.identity C₂ x₂))
          (Category.identity (category-sum F) (base x₂))
      map-identity _
        = Category.arrow-refl (category-sum F)

      map-compose
        : {x₂ y₂ z₂ : Category.Object C₂}
        → (f₂ : Category.Arrow C₂ y₂ z₂)
        → (g₂ : Category.Arrow C₂ x₂ y₂)
        → Category.ArrowEqual (category-sum F)
          (map (Category.compose C₂ f₂ g₂))
          (Category.compose (category-sum F) (map f₂) (map g₂))
      map-compose _ _
        = Category.arrow-refl (category-sum F)

  functor-sum₂
    : (F : Functor C₂ C₁)
    → Functor C₂ (category-sum F)
  functor-sum₂ F
    = record {FunctorSum₂ F}

-- ## FunctorEqual

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₂ C₁}
  {G : Functor D₂ D₁}
  {H₁₁ H₁₂ : Functor C₁ D₁}
  {H₂₁ H₂₂ : Functor C₂ D₂}
  where

  module FunctorEqualSum
    (s₁ : FunctorSquare H₂₁ H₁₁ F G)
    (s₂ : FunctorSquare H₂₂ H₁₂ F G)
    (p₁ : FunctorEqual H₁₁ H₁₂)
    (p₂ : FunctorEqual H₂₁ H₂₂)
    where

    base
      : (x : Category.Object (category-sum F))
      → Functor.base (functor-sum s₁) x ≅ Functor.base (functor-sum s₂) x
    base (ι₁ x₁)
      = sub ι₁ (FunctorEqual.base p₁ x₁)
    base (ι₂ x₂)
      = sub ι₂ (FunctorEqual.base p₂ x₂)
  
    map
      : {x y : Category.Object (category-sum F)}
      → (f : Category.Arrow (category-sum F) x y)
      → Category'.ArrowEqual'
        (category-sum G)
        (category-sum G)
        (Functor.map (functor-sum s₁) f)
        (Functor.map (functor-sum s₂) f)
    map {x = x} {y = y} (CategorySum.arrow₁ f₁)
      = arrow-equal₁ G (base x) (base y)
      $ Category.arrow-trans' D₁ (Category.arrow-equal' D₁
        (FunctorSum.base-equal s₁ x)
        (FunctorSum.base-equal s₁ y)
        (Functor.map H₁₁ f₁))
      $ Category.arrow-trans' D₁ (FunctorEqual.map p₁ f₁)
      $ Category.arrow-sym' D₁ (Category.arrow-equal' D₁
        (FunctorSum.base-equal s₂ x)
        (FunctorSum.base-equal s₂ y)
        (Functor.map H₁₂ f₁))
    map (CategorySum.arrow₂ f₂)
      = arrow-equal₂ G (FunctorEqual.map p₂ f₂)

  functor-equal-sum
    : (s₁ : FunctorSquare H₂₁ H₁₁ F G)
    → (s₂ : FunctorSquare H₂₂ H₁₂ F G)
    → FunctorEqual H₁₁ H₁₂
    → FunctorEqual H₂₁ H₂₂
    → FunctorEqual
      (functor-sum s₁)
      (functor-sum s₂)
  functor-equal-sum s₁ s₂ p₁ p₂
    = record {FunctorEqualSum s₁ s₂ p₁ p₂}

-- ## FunctorIdentity

functor-identity-sum
  : {C₁ C₂ : Category}
  → {F : Functor C₂ C₁}
  → {G₁ : Functor C₁ C₁}
  → {G₂ : Functor C₂ C₂}
  → (s : FunctorSquare G₂ G₁ F F)
  → FunctorIdentity G₁
  → FunctorIdentity G₂
  → FunctorIdentity
    (functor-sum s)
functor-identity-sum {F = F} s p₁ p₂
  = functor-identity-from-equal
  $ functor-trans (functor-equal-sum s
    (functor-square-identity' F)
    (functor-identity-to-equal p₁)
    (functor-identity-to-equal p₂))
  $ functor-sum-identity F

-- ## FunctorCompose

functor-compose-sum
  : {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  → {F : Functor C₂ C₁}
  → {G : Functor D₂ D₁}
  → {H : Functor E₂ E₁}
  → {I₁ : Functor D₁ E₁}
  → {I₂ : Functor D₂ E₂}
  → {J₁ : Functor C₁ D₁}
  → {J₂ : Functor C₂ D₂}
  → {K₁ : Functor C₁ E₁}
  → {K₂ : Functor C₂ E₂}
  → (s : FunctorSquare I₂ I₁ G H)
  → (t : FunctorSquare J₂ J₁ F G)
  → (u : FunctorSquare K₂ K₁ F H)
  → FunctorCompose I₁ J₁ K₁
  → FunctorCompose I₂ J₂ K₂
  → FunctorCompose
    (functor-sum s)
    (functor-sum t)
    (functor-sum u)
functor-compose-sum s t u p₁ p₂
  = functor-compose-from-equal
    (functor-sum s)
    (functor-sum t)
  $ functor-trans (functor-equal-sum u
    (functor-square-compose' s t)
    (functor-compose-to-equal p₁)
    (functor-compose-to-equal p₂))
  $ functor-sum-compose s t

-- ## FunctorSquare

functor-square-sum
  : {C₁₁ C₁₂ C₂₁ C₂₂ D₁₁ D₁₂ D₂₁ D₂₂ : Category}
  → {F₁ : Functor C₂₁ C₁₁}
  → {F₂ : Functor C₂₂ C₁₂}
  → {G₁ : Functor D₂₁ D₁₁}
  → {G₂ : Functor D₂₂ D₁₂}
  → {H₁ : Functor C₁₁ C₁₂}
  → {H₂ : Functor C₂₁ C₂₂}
  → {I₁ : Functor D₁₁ D₁₂}
  → {I₂ : Functor D₂₁ D₂₂}
  → {J₁₁ : Functor C₁₁ D₁₁}
  → {J₁₂ : Functor C₁₂ D₁₂}
  → {J₂₁ : Functor C₂₁ D₂₁}
  → {J₂₂ : Functor C₂₂ D₂₂}
  → (s : FunctorSquare H₂ H₁ F₁ F₂)
  → (t : FunctorSquare I₂ I₁ G₁ G₂)
  → (u₁ : FunctorSquare J₂₁ J₁₁ F₁ G₁)
  → (u₂ : FunctorSquare J₂₂ J₁₂ F₂ G₂)
  → FunctorSquare H₁ I₁ J₁₁ J₁₂
  → FunctorSquare H₂ I₂ J₂₁ J₂₂
  → FunctorSquare
    (functor-sum s)
    (functor-sum t)
    (functor-sum u₁)
    (functor-sum u₂)
functor-square-sum s t u₁ u₂ p₁ p₂
  = functor-square-from-equal
    (functor-sum s)
    (functor-sum t)
    (functor-sum u₁)
    (functor-sum u₂)
  $ functor-trans (functor-sym
    (functor-sum-compose u₂ s))
  $ functor-trans (functor-equal-sum
    (functor-square-compose' u₂ s)
    (functor-square-compose' t u₁)
    (functor-square-to-equal p₁)
    (functor-square-to-equal p₂))
  $ functor-sum-compose t u₁

-- ## FunctorSquare₂

functor-square-sum₂
  : {C₁₁ C₁₂ C₂₁ C₂₂ : Category}
  → {F₁ : Functor C₂₁ C₁₁}
  → {F₂ : Functor C₂₂ C₁₂}
  → {G₁ : Functor C₁₁ C₁₂}
  → {G₂ : Functor C₂₁ C₂₂}
  → (s : FunctorSquare G₂ G₁ F₁ F₂)
  → FunctorSquare G₂
    (functor-sum s)
    (functor-sum₂ F₁)
    (functor-sum₂ F₂)
functor-square-sum₂ {F₂ = F₂} _
  = record
  { base
    = λ _ → refl
  ; map
    = λ _ → Category.arrow-refl' (category-sum F₂)
  }

