module Prover.Category.Sum where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare; functor-compose'; functor-compose-from-equal;
    functor-compose-to-equal; functor-identity'; functor-identity-from-equal;
    functor-identity-to-equal; functor-square-compose';
    functor-square-identity'; functor-square-from-equal;
    functor-square-to-equal; functor-sym; functor-trans)
open import Prover.Prelude

-- ## Category

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

    identity
      : (x : Object)
      → Arrow x x
    identity (ι₁ x₁)
      = arrow₁ (Category.identity C₁ x₁)
    identity (ι₂ x₂)
      = arrow₂ (Category.identity C₂ x₂)

    compose
      : {x y z : Object}
      → Arrow y z
      → Arrow x y
      → Arrow x z
    compose (arrow₁ f₁) (arrow₁ g₁)
      = arrow₁ (Category.compose C₁ f₁ g₁)
    compose (arrow₁ f₁) (arrow₂ g₂)
      = arrow₁ (Category.compose C₁ f₁ (Functor.map F g₂))
    compose (arrow₂ f₂) (arrow₁ g₁)
      = arrow₁ (Category.compose C₁ (Functor.map F f₂) g₁)
    compose (arrow₂ f₂) (arrow₂ g₂)
      = arrow₂ (Category.compose C₂ f₂ g₂)

    abstract

      precompose
        : {x y : Object}
        → (f : Arrow x y)
        → compose f (identity x) ≡ f
      precompose {x = ι₁ _} (arrow₁ f₁)
        = sub arrow₁ (Category.precompose C₁ f₁)
      precompose {x = ι₂ x₂} (arrow₁ f₁)
        with Functor.map F (Category.identity C₂ x₂)
        | Functor.map-identity F x₂
      ... | _ | refl
        = sub arrow₁ (Category.precompose C₁ f₁)
      precompose (arrow₂ f₂)
        = sub arrow₂ (Category.precompose C₂ f₂)
  
      postcompose
        : {x y : Object}
        → (f : Arrow x y)
        → compose (identity y) f ≡ f
      postcompose {y = ι₁ _} (arrow₁ f₁)
        = sub arrow₁ (Category.postcompose C₁ f₁)
      postcompose {y = ι₂ y₂} (arrow₁ f₁)
        with Functor.map F (Category.identity C₂ y₂)
        | Functor.map-identity F y₂
      ... | _ | refl
        = sub arrow₁ (Category.postcompose C₁ f₁)
      postcompose (arrow₂ f₂)
        = sub arrow₂ (Category.postcompose C₂ f₂)
  
      associative
        : {w x y z : Object}
        → (f : Arrow y z)
        → (g : Arrow x y)
        → (h : Arrow w x)
        → compose (compose f g) h ≡ compose f (compose g h)
      associative (arrow₁ f₁) (arrow₁ g₁) (arrow₁ h₁)
        = sub arrow₁ (Category.associative C₁ f₁ g₁ h₁)
      associative (arrow₁ f₁) (arrow₁ g₁) (arrow₂ h₂)
        = sub arrow₁ (Category.associative C₁ f₁ g₁ (Functor.map F h₂))
      associative (arrow₁ f₁) (arrow₂ g₂) (arrow₁ h₁)
        = sub arrow₁ (Category.associative C₁ f₁ (Functor.map F g₂) h₁)
      associative (arrow₁ f₁) (arrow₂ g₂) (arrow₂ h₂)
        with Functor.map F (Category.compose C₂ g₂ h₂)
        | Functor.map-compose F g₂ h₂
      ... | _ | refl
        = sub arrow₁ (Category.associative C₁ f₁ (Functor.map F g₂)
          (Functor.map F h₂))
      associative (arrow₂ f₂) (arrow₁ g₁) (arrow₁ h₁)
        = sub arrow₁ (Category.associative C₁ (Functor.map F f₂) g₁ h₁)
      associative (arrow₂ f₂) (arrow₁ g₁) (arrow₂ h₂)
        = sub arrow₁ (Category.associative C₁ (Functor.map F f₂) g₁
          (Functor.map F h₂))
      associative (arrow₂ f₂) (arrow₂ g₂) (arrow₁ h₁)
        with Functor.map F (Category.compose C₂ f₂ g₂)
        | Functor.map-compose F f₂ g₂
      ... | _ | refl
        = sub arrow₁ (Category.associative C₁ (Functor.map F f₂)
          (Functor.map F g₂) h₁)
      associative (arrow₂ f₂) (arrow₂ g₂) (arrow₂ h₂)
        = sub arrow₂ (Category.associative C₂ f₂ g₂ h₂)

  category-sum
    : Functor C₂ C₁
    → Category
  category-sum F
    = record {CategorySum F}

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

    base-eq
      : (x : Category.Object (category-sum F))
      → CategorySum.object₁ G (base x)
        ≡ Functor.base H₁ (CategorySum.object₁ F x)
    base-eq (ι₁ _)
      = refl
    base-eq (ι₂ x₂)
      = FunctorSquare.base s x₂

    map
      : {x y : Category.Object (category-sum F)}
      → Category.Arrow (category-sum F) x y
      → Category.Arrow (category-sum G) (base x) (base y)
    map {x = x} {y = y} (CategorySum.arrow₁ f₁)
      = CategorySum.arrow₁
        (Category.arrow D₁ (base-eq x) (base-eq y) (Functor.map H₁ f₁))
    map (CategorySum.arrow₂ f₂)
      = CategorySum.arrow₂
        (Functor.map H₂ f₂)

    abstract

      map-identity
        : (x : Category.Object (category-sum F))
        → map (Category.identity (category-sum F) x)
          ≡ Category.identity (category-sum G) (base x)
      map-identity (ι₁ x₁)
        = sub CategorySum.arrow₁ (Functor.map-identity H₁ x₁)
      map-identity (ι₂ x₂)
        = sub CategorySum.arrow₂ (Functor.map-identity H₂ x₂)

      map-compose₁
        : {x₁ y₁ z₁ : Category.Object C₁}
        → {x₁' y₁' z₁' : Category.Object D₁}
        → (p₁ : x₁' ≡ Functor.base H₁ x₁)
        → (q₁ : y₁' ≡ Functor.base H₁ y₁)
        → (r₁ : z₁' ≡ Functor.base H₁ z₁)
        → (f₁ : Category.Arrow C₁ y₁ z₁)
        → (g₁ : Category.Arrow C₁ x₁ y₁)
        → Category.arrow D₁ p₁ r₁
          (Functor.map H₁ (Category.compose C₁ f₁ g₁))
        ≡ Category.compose D₁
          (Category.arrow D₁ q₁ r₁ (Functor.map H₁ f₁))
          (Category.arrow D₁ p₁ q₁ (Functor.map H₁ g₁))
      map-compose₁ refl refl refl
        = Functor.map-compose H₁
  
      map-compose₁'
        : (x y z : Category.Object C₁ ⊔ Category.Object C₂)
        → (f₁ : Category.Arrow C₁
          (CategorySum.object₁ F y)
          (CategorySum.object₁ F z))
        → (g₁ : Category.Arrow C₁
          (CategorySum.object₁ F x)
          (CategorySum.object₁ F y))
        → Category.arrow D₁ (base-eq x) (base-eq z)
          (Functor.map H₁ (Category.compose C₁ f₁ g₁))
        ≡ Category.compose D₁
          (Category.arrow D₁ (base-eq y) (base-eq z) (Functor.map H₁ f₁))
          (Category.arrow D₁ (base-eq x) (base-eq y) (Functor.map H₁ g₁))
      map-compose₁' x y z f₁ g₁
        = map-compose₁ (base-eq x) (base-eq y) (base-eq z) f₁ g₁
  
      map-compose
        : {x y z : Category.Object (category-sum F)}
        → (f : Category.Arrow (category-sum F) y z)
        → (g : Category.Arrow (category-sum F) x y)
        → map (Category.compose (category-sum F) f g)
          ≡ Category.compose (category-sum G) (map f) (map g)
      map-compose {x = x} {y = y} {z = z}
        (CategorySum.arrow₁ f₁) (CategorySum.arrow₁ g₁)
        = sub CategorySum.arrow₁
        $ map-compose₁' x y z f₁ g₁
      map-compose {x = x} {y = y} {z = z}
        (CategorySum.arrow₁ f₁) (CategorySum.arrow₂ g₂)
        = sub CategorySum.arrow₁
        $ trans
          (map-compose₁' x y z f₁
            (Functor.map F g₂))
        $ sub (λ g₁ → Category.compose D₁
          (Category.arrow D₁ (base-eq y) (base-eq z)
            (Functor.map H₁ f₁)) g₁)
        $ trans
          (Category.arrow-eq D₁ (base-eq x) (base-eq y)
            (Functor.map H₁ (Functor.map F g₂)))
        $ sym (FunctorSquare.map s g₂)
      map-compose {x = x} {y = y} {z = z}
        (CategorySum.arrow₂ f₂) (CategorySum.arrow₁ g₁)
        = sub CategorySum.arrow₁
        $ trans
          (map-compose₁' x y z
            (Functor.map F f₂) g₁)
        $ sub (λ f₁ → Category.compose D₁ f₁
          (Category.arrow D₁ (base-eq x) (base-eq y)
            (Functor.map H₁ g₁)))
        $ trans
          (Category.arrow-eq D₁ (base-eq y) (base-eq z)
            (Functor.map H₁ (Functor.map F f₂)))
        $ sym (FunctorSquare.map s f₂)
      map-compose (CategorySum.arrow₂ f₂) (CategorySum.arrow₂ g₂)
        = sub CategorySum.arrow₂
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
      → Functor.map (functor-sum (functor-square-identity' F)) f
        ≅ Functor.map (functor-identity' (category-sum F)) f
    map {x = ι₁ _} {y = ι₁ _} (CategorySum.arrow₁ _)
      = refl
    map {x = ι₁ _} {y = ι₂ _} (CategorySum.arrow₁ _)
      = refl
    map {x = ι₂ _} {y = ι₁ _} (CategorySum.arrow₁ _)
      = refl
    map {x = ι₂ _} {y = ι₂ _} (CategorySum.arrow₁ _)
      = refl
    map (CategorySum.arrow₂ _)
      = refl

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
  
    arrow-eq₁₂
      : {x₁ y₁₁ y₂₁ : Category.Object E₁}
      → {f₁ : Category.Arrow E₁ x₁ y₁₁}
      → {f₂ : Category.Arrow E₁ x₁ y₂₁}
      → (y₂ : Category.Object E₂)
      → (q₁ : Functor.base H y₂ ≡ y₁₁)
      → (q₂ : Functor.base H y₂ ≡ y₂₁)
      → f₁ ≅ f₂
      → CategorySum.arrow₁ {F = H} {x = ι₁ x₁} {y = ι₂ y₂}
        (Category.arrow E₁ refl q₁ f₁)
      ≅ CategorySum.arrow₁ {F = H} {x = ι₁ x₁} {y = ι₂ y₂}
        (Category.arrow E₁ refl q₂ f₂)
    arrow-eq₁₂ _ refl refl refl
      = refl

    arrow-eq₂₁
      : {x₁₁ x₂₁ y₁ : Category.Object E₁}
      → {f₁ : Category.Arrow E₁ x₁₁ y₁}
      → {f₂ : Category.Arrow E₁ x₂₁ y₁}
      → (x₂ : Category.Object E₂)
      → (p₁ : Functor.base H x₂ ≡ x₁₁)
      → (p₂ : Functor.base H x₂ ≡ x₂₁)
      → f₁ ≅ f₂
      → CategorySum.arrow₁ {F = H} {x = ι₂ x₂} {y = ι₁ y₁}
        (Category.arrow E₁ p₁ refl f₁)
      ≅ CategorySum.arrow₁ {F = H} {x = ι₂ x₂} {y = ι₁ y₁}
        (Category.arrow E₁ p₂ refl f₂)
    arrow-eq₂₁ _ refl refl refl
      = refl

    arrow-eq₂₂
      : {x₁₁ x₂₁ y₁₁ y₂₁ : Category.Object E₁}
      → {f₁ : Category.Arrow E₁ x₁₁ y₁₁}
      → {f₂ : Category.Arrow E₁ x₂₁ y₂₁}
      → (x₂ y₂ : Category.Object E₂)
      → (p₁ : Functor.base H x₂ ≡ x₁₁)
      → (p₂ : Functor.base H x₂ ≡ x₂₁)
      → (q₁ : Functor.base H y₂ ≡ y₁₁)
      → (q₂ : Functor.base H y₂ ≡ y₂₁)
      → f₁ ≅ f₂
      → CategorySum.arrow₁ {F = H} {x = ι₂ x₂} {y = ι₂ y₂}
        (Category.arrow E₁ p₁ q₁ f₁)
      ≅ CategorySum.arrow₁ {F = H} {x = ι₂ x₂} {y = ι₂ y₂}
        (Category.arrow E₁ p₂ q₂ f₂)
    arrow-eq₂₂ _ _ refl refl refl refl refl
      = refl

    map-eq
      : {x₁ y₁ : Category.Object C₁}
      → {x₁' y₁' : Category.Object D₁}
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → (p₁ : x₁' ≡ Functor.base J₁ x₁)
      → (q₁ : y₁' ≡ Functor.base J₁ y₁)
      → Functor.map I₁ (Functor.map J₁ f₁)
        ≅ Functor.map I₁ (Category.arrow D₁ p₁ q₁ (Functor.map J₁ f₁))
    map-eq _ refl refl
      = refl

    map
      : {x y : Category.Object (category-sum F)}
      → (f : Category.Arrow (category-sum F) x y)
      → Functor.map (functor-sum (functor-square-compose' s t)) f
        ≅ Functor.map (functor-compose' (functor-sum s) (functor-sum t)) f
    map {x = ι₁ _} {y = ι₁ _} (CategorySum.arrow₁ _)
      = refl
    map {x = ι₁ _} {y = ι₂ y₂} (CategorySum.arrow₁ f₁)
      = arrow-eq₁₂
        (Functor.base I₂ (Functor.base J₂ y₂))
        (FunctorSquare.base (functor-square-compose' s t) y₂)
        (FunctorSquare.base s (Functor.base J₂ y₂))
        (map-eq f₁ refl (FunctorSquare.base t y₂))
    map {x = ι₂ x₂} {y = ι₁ _} (CategorySum.arrow₁ f₁)
      = arrow-eq₂₁
        (Functor.base I₂ (Functor.base J₂ x₂))
        (FunctorSquare.base (functor-square-compose' s t) x₂)
        (FunctorSquare.base s (Functor.base J₂ x₂))
        (map-eq f₁ (FunctorSquare.base t x₂) refl)
    map {x = ι₂ x₂} {y = ι₂ y₂} (CategorySum.arrow₁ f₁)
      = arrow-eq₂₂
        (Functor.base I₂ (Functor.base J₂ x₂))
        (Functor.base I₂ (Functor.base J₂ y₂))
        (FunctorSquare.base (functor-square-compose' s t) x₂)
        (FunctorSquare.base s (Functor.base J₂ x₂))
        (FunctorSquare.base (functor-square-compose' s t) y₂)
        (FunctorSquare.base s (Functor.base J₂ y₂))
        (map-eq f₁ (FunctorSquare.base t x₂) (FunctorSquare.base t y₂))
    map (CategorySum.arrow₂ _)
      = refl

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
  {C D₁ D₂ : Category}
  where

  module FunctorSum₂
    (F : Functor D₂ D₁)
    (G : Functor C D₂)
    where

    base
      : Category.Object C
      → Category.Object (category-sum F)
    base x
      = ι₂ (Functor.base G x)

    map
      : {x y : Category.Object C}
      → Category.Arrow C x y
      → Category.Arrow (category-sum F) (base x) (base y)
    map f
      = CategorySum.arrow₂ (Functor.map G f)

    abstract

      map-identity
        : (x : Category.Object C)
        → map (Category.identity C x)
          ≡ Category.identity (category-sum F) (base x)
      map-identity x
        = sub CategorySum.arrow₂ (Functor.map-identity G x)
  
      map-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → map (Category.compose C f g)
          ≡ Category.compose (category-sum F) (map f) (map g)
      map-compose f g
        = sub CategorySum.arrow₂ (Functor.map-compose G f g)

  functor-sum₂
    : (F : Functor D₂ D₁)
    → Functor C D₂
    → Functor C (category-sum F)
  functor-sum₂ F G
    = record {FunctorSum₂ F G}

-- ## FunctorEqual

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₂ C₁}
  {G : Functor D₂ D₁}
  {H₁₁ H₂₁ : Functor C₁ D₁}
  {H₁₂ H₂₂ : Functor C₂ D₂}
  where

  module FunctorEqualSum
    (s₁ : FunctorSquare H₁₂ H₁₁ F G)
    (s₂ : FunctorSquare H₂₂ H₂₁ F G)
    (p₁ : FunctorEqual H₁₁ H₂₁)
    (p₂ : FunctorEqual H₁₂ H₂₂)
    where

    base
      : (x : Category.Object (category-sum F))
      → Functor.base (functor-sum s₁) x ≅ Functor.base (functor-sum s₂) x
    base (ι₁ x₁)
      with Functor.base H₁₁ x₁
      | FunctorEqual.base p₁ x₁
    ... | _ | refl
      = refl
    base (ι₂ x₂)
      with Functor.base H₁₂ x₂
      | FunctorEqual.base p₂ x₂
    ... | _ | refl
      = refl

    arrow-eq₁₂
      : {x₁₁ x₂₁ y₁₁ y₂₁ : Category.Object D₁}
      → {y₁₂ y₂₂ : Category.Object D₂}
      → {f₁ : Category.Arrow D₁ x₁₁ y₁₁}
      → {f₂ : Category.Arrow D₁ x₂₁ y₂₁}
      → (q₁ : Functor.base G y₁₂ ≡ y₁₁)
      → (q₂ : Functor.base G y₂₂ ≡ y₂₁)
      → x₁₁ ≡ x₂₁
      → y₁₂ ≡ y₂₂
      → f₁ ≅ f₂
      → CategorySum.arrow₁ {F = G} {x = ι₁ x₁₁} {y = ι₂ y₁₂}
        (Category.arrow D₁ refl q₁ f₁)
      ≅ CategorySum.arrow₁ {F = G} {x = ι₁ x₂₁} {y = ι₂ y₂₂}
        (Category.arrow D₁ refl q₂ f₂)
    arrow-eq₁₂ refl refl refl refl refl
      = refl

    arrow-eq₂₁
      : {x₁₁ x₂₁ y₁₁ y₂₁ : Category.Object D₁}
      → {x₁₂ x₂₂ : Category.Object D₂}
      → {f₁ : Category.Arrow D₁ x₁₁ y₁₁}
      → {f₂ : Category.Arrow D₁ x₂₁ y₂₁}
      → (p₁ : Functor.base G x₁₂ ≡ x₁₁)
      → (p₂ : Functor.base G x₂₂ ≡ x₂₁)
      → x₁₂ ≡ x₂₂
      → y₁₁ ≡ y₂₁
      → f₁ ≅ f₂
      → CategorySum.arrow₁ {F = G} {x = ι₂ x₁₂} {y = ι₁ y₁₁}
        (Category.arrow D₁ p₁ refl f₁)
      ≅ CategorySum.arrow₁ {F = G} {x = ι₂ x₂₂} {y = ι₁ y₂₁}
        (Category.arrow D₁ p₂ refl f₂)
    arrow-eq₂₁ refl refl refl refl refl
      = refl

    arrow-eq₂₂
      : {x₁₁ x₂₁ y₁₁ y₂₁ : Category.Object D₁}
      → {x₁₂ x₂₂ y₁₂ y₂₂ : Category.Object D₂}
      → {f₁ : Category.Arrow D₁ x₁₁ y₁₁}
      → {f₂ : Category.Arrow D₁ x₂₁ y₂₁}
      → (p₁ : Functor.base G x₁₂ ≡ x₁₁)
      → (p₂ : Functor.base G x₂₂ ≡ x₂₁)
      → (q₁ : Functor.base G y₁₂ ≡ y₁₁)
      → (q₂ : Functor.base G y₂₂ ≡ y₂₁)
      → x₁₂ ≡ x₂₂
      → y₁₂ ≡ y₂₂
      → f₁ ≅ f₂
      → CategorySum.arrow₁ {F = G} {x = ι₂ x₁₂} {y = ι₂ y₁₂}
        (Category.arrow D₁ p₁ q₁ f₁)
      ≅ CategorySum.arrow₁ {F = G} {x = ι₂ x₂₂} {y = ι₂ y₂₂}
        (Category.arrow D₁ p₂ q₂ f₂)
    arrow-eq₂₂ refl refl refl refl refl refl refl
      = refl

    map
      : {x y : Category.Object (category-sum F)}
      → (f : Category.Arrow (category-sum F) x y)
      → Functor.map (functor-sum s₁) f ≅ Functor.map (functor-sum s₂) f

    map {x = ι₁ x₁} {y = ι₁ y₁} (CategorySum.arrow₁ f₁)
      with Functor.base H₁₁ x₁
      | FunctorEqual.base p₁ x₁
      | Functor.base H₁₁ y₁
      | FunctorEqual.base p₁ y₁
      | Functor.map H₁₁ f₁
      | FunctorEqual.map p₁ f₁
    ... | _ | refl | _ | refl | _ | refl
      = refl
    map {x = ι₂ x₂} {y = ι₂ y₂} (CategorySum.arrow₂ f₂)
      with Functor.base H₁₂ x₂
      | FunctorEqual.base p₂ x₂
      | Functor.base H₁₂ y₂
      | FunctorEqual.base p₂ y₂
      | Functor.map H₁₂ f₂
      | FunctorEqual.map p₂ f₂
    ... | _ | refl | _ | refl | _ | refl
      = refl

    map {x = ι₁ x₁} {y = ι₂ y₂} (CategorySum.arrow₁ f₁)
      = arrow-eq₁₂
        (FunctorSquare.base s₁ y₂)
        (FunctorSquare.base s₂ y₂)
        (FunctorEqual.base p₁ x₁)
        (FunctorEqual.base p₂ y₂)
        (FunctorEqual.map p₁ f₁)
    map {x = ι₂ x₂} {y = ι₁ y₁} (CategorySum.arrow₁ f₁)
      = arrow-eq₂₁
        (FunctorSquare.base s₁ x₂)
        (FunctorSquare.base s₂ x₂)
        (FunctorEqual.base p₂ x₂)
        (FunctorEqual.base p₁ y₁)
        (FunctorEqual.map p₁ f₁)
    map {x = ι₂ x₂} {y = ι₂ y₂} (CategorySum.arrow₁ f₁)
      = arrow-eq₂₂
        (FunctorSquare.base s₁ x₂)
        (FunctorSquare.base s₂ x₂)
        (FunctorSquare.base s₁ y₂)
        (FunctorSquare.base s₂ y₂)
        (FunctorEqual.base p₂ x₂)
        (FunctorEqual.base p₂ y₂)
        (FunctorEqual.map p₁ f₁)

  functor-equal-sum
    : (s₁ : FunctorSquare H₁₂ H₁₁ F G)
    → (s₂ : FunctorSquare H₂₂ H₂₁ F G)
    → FunctorEqual H₁₁ H₂₁
    → FunctorEqual H₁₂ H₂₂
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
  $ functor-trans
    (functor-equal-sum s
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
  $ functor-trans
    (functor-equal-sum u
      (functor-square-compose' s t)
      (functor-compose-to-equal p₁)
      (functor-compose-to-equal p₂))
  $ functor-sum-compose s t

-- ## FunctorSquare

functor-square-sum
  : {C₁₁ C₁₂ C₂₁ C₂₂ D₁₁ D₁₂ D₂₁ D₂₂ : Category}
  → {F₁ : Functor C₁₂ C₁₁}
  → {F₂ : Functor C₂₂ C₂₁}
  → {G₁ : Functor D₁₂ D₁₁}
  → {G₂ : Functor D₂₂ D₂₁}
  → {H₁ : Functor C₁₁ C₂₁}
  → {H₂ : Functor C₁₂ C₂₂}
  → {I₁ : Functor D₁₁ D₂₁}
  → {I₂ : Functor D₁₂ D₂₂}
  → {J₁₁ : Functor C₁₁ D₁₁}
  → {J₁₂ : Functor C₁₂ D₁₂}
  → {J₂₁ : Functor C₂₁ D₂₁}
  → {J₂₂ : Functor C₂₂ D₂₂}
  → (s : FunctorSquare H₂ H₁ F₁ F₂)
  → (t : FunctorSquare I₂ I₁ G₁ G₂)
  → (u₁ : FunctorSquare J₁₂ J₁₁ F₁ G₁)
  → (u₂ : FunctorSquare J₂₂ J₂₁ F₂ G₂)
  → FunctorSquare H₁ I₁ J₁₁ J₂₁
  → FunctorSquare H₂ I₂ J₁₂ J₂₂
  → FunctorSquare
    (functor-sum s)
    (functor-sum t)
    (functor-sum u₁)
    (functor-sum u₂)
functor-square-sum s t u₁ u₂ p₁ p₂
  = functor-square-from-equal
  $ functor-trans (functor-sym
    (functor-sum-compose u₂ s))
  $ functor-trans
    (functor-equal-sum
      (functor-square-compose' u₂ s)
      (functor-square-compose' t u₁)
      (functor-square-to-equal p₁)
      (functor-square-to-equal p₂))
  $ functor-sum-compose t u₁

-- ## FunctorSquare₂

module _
  {C₁ C₂ D₁₁ D₁₂ D₂₁ D₂₂ : Category}
  {F₁ : Functor D₁₂ D₁₁}
  {F₂ : Functor D₂₂ D₂₁}
  {G : Functor C₁ C₂}
  {H₁ : Functor D₁₁ D₂₁}
  {H₂ : Functor D₁₂ D₂₂}
  {I₁ : Functor C₁ D₁₂}
  {I₂ : Functor C₂ D₂₂}
  where

  module FunctorSquareSum₂
    (s : FunctorSquare H₂ H₁ F₁ F₂)
    (t : FunctorSquare G H₂ I₁ I₂)
    where

    base
      : (x₁ : Category.Object C₁)
      → Functor.base (functor-sum₂ F₂ I₂) (Functor.base G x₁) 
        ≅ Functor.base (functor-sum s) (Functor.base (functor-sum₂ F₁ I₁) x₁)
    base x₁
      with Functor.base I₂ (Functor.base G x₁)
      | FunctorSquare.base t x₁
    ... | _ | refl
      = refl
  
    map
      : {x₁ y₁ : Category.Object C₁}
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Functor.map (functor-sum₂ F₂ I₂) (Functor.map G f₁)
        ≅ Functor.map (functor-sum s) (Functor.map (functor-sum₂ F₁ I₁) f₁)
    map {x₁ = x₁} {y₁ = y₁} f₁
      with Functor.base I₂ (Functor.base G x₁)
      | FunctorSquare.base t x₁
      | Functor.base I₂ (Functor.base G y₁)
      | FunctorSquare.base t y₁
      | Functor.map I₂ (Functor.map G f₁)
      | FunctorSquare.map t f₁
    ... | _ | refl | _ | refl | _ | refl
      = refl

  functor-square-sum₂
    : (s : FunctorSquare H₂ H₁ F₁ F₂)
    → FunctorSquare G H₂ I₁ I₂
    → FunctorSquare G
      (functor-sum s)
      (functor-sum₂ F₁ I₁)
      (functor-sum₂ F₂ I₂)
  functor-square-sum₂ s t
    = record {FunctorSquareSum₂ s t}

