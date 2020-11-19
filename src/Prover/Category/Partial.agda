module Prover.Category.Partial where

open import Prover.Category
  using (Category; Functor; FunctorSquare; Precategory)
open import Prover.Function.Partial
  using (PartialFunction; PartialFunctionSquare)
open import Prover.Prelude

-- ## PartialPrefunctor

record PartialPrefunctor
  (C : Category)
  (D : Precategory)
  : Set
  where

  no-eta-equality

  field

    base
      : Category.Object C
      → Maybe (Precategory.Object D)

    map
      : {x y : Category.Object C}
      → {x' y' : Precategory.Object D}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow C x y
      → Precategory.Arrow D x' y'

    map-equal
      : {x y : Category.Object C}
      → {x' y' : Precategory.Object D}
      → {f₁ f₂ : Category.Arrow C x y}
      → (p : base x ≡ just x')
      → (q : base y ≡ just y')
      → Category.ArrowEqual C f₁ f₂
      → Precategory.ArrowEqual D (map p q f₁) (map p q f₂)

    map-identity
      : {x' : Precategory.Object D}
      → (x : Category.Object C)
      → (p : base x ≡ just x')
      → Precategory.ArrowEqual D
        (map p p (Category.identity C x))
        (Precategory.identity D x')

    map-compose
      : {x y z : Category.Object C}
      → {x' y' z' : Precategory.Object D}
      → (p : base x ≡ just x')
      → (q : base y ≡ just y')
      → (r : base z ≡ just z')
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → Precategory.ArrowEqual D
        (map p r (Category.compose C f g))
        (Precategory.compose D (map q r f) (map p q g))

-- ## PartialFunctor

-- ### Definition

record PartialFunctor
  (C D : Category)
  : Set
  where

  no-eta-equality

  field

    base
      : Category.Object C
      → Maybe (Category.Object D)

  partial-function
    : PartialFunction
      (Category.Object C)
      (Category.Object D)
  partial-function
    = record
    { base
      = base
    }

  open PartialFunction partial-function public
    using (bool-function)

  field

    map
      : {x y : Category.Object C}
      → {x' y' : Category.Object D}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow C x y
      → Category.Arrow D x' y'

    map-equal
      : {x y : Category.Object C}
      → {x' y' : Category.Object D}
      → {f₁ f₂ : Category.Arrow C x y}
      → (p : base x ≡ just x')
      → (q : base y ≡ just y')
      → Category.ArrowEqual C f₁ f₂
      → Category.ArrowEqual D (map p q f₁) (map p q f₂)

    map-identity
      : {x' : Category.Object D}
      → (x : Category.Object C)
      → (p : base x ≡ just x')
      → Category.ArrowEqual D
        (map p p (Category.identity C x))
        (Category.identity D x')

    map-compose
      : {x y z : Category.Object C}
      → {x' y' z' : Category.Object D}
      → (p : base x ≡ just x')
      → (q : base y ≡ just y')
      → (r : base z ≡ just z')
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → Category.ArrowEqual D
        (map p r (Category.compose C f g))
        (Category.compose D (map q r f) (map p q g))

  map-equal'
    : {x₁ x₂ y₁ y₂ : Category.Object C}
    → {x₁' x₂' y₁' y₂' : Category.Object D}
    → {f₁ : Category.Arrow C x₁ y₁}
    → {f₂ : Category.Arrow C x₂ y₂}
    → (p₁ : base x₁ ≡ just x₁')
    → (p₂ : base x₂ ≡ just x₂')
    → (q₁ : base y₁ ≡ just y₁')
    → (q₂ : base y₂ ≡ just y₂')
    → Category.ArrowEqual' C f₁ f₂
    → Category.ArrowEqual' D (map p₁ q₁ f₁) (map p₂ q₂ f₂)
  map-equal' p₁ p₂ q₁ q₂ (Category.any r)
    with trans (sym p₁) p₂
    | trans (sym q₁) q₂
  ... | refl | refl
    with irrelevant p₁ p₂
    | irrelevant q₁ q₂
  ... | refl | refl
    = Category.any
    $ map-equal p₁ q₁ r

  map-identity'
    : {x₁' x₂' : Category.Object D}
    → (x : Category.Object C)
    → (p₁ : base x ≡ just x₁')
    → (p₂ : base x ≡ just x₂')
    → Category.ArrowEqual' D
      (map p₁ p₂ (Category.identity C x))
      (Category.identity D x₂')
  map-identity' x p₁ p₂
    with trans (sym p₁) p₂
  ... | refl
    with irrelevant p₁ p₂
  ... | refl
    = Category.any
    $ map-identity x p₁

  map-compose'
    : {x y z : Category.Object C}
    → {x' y' z' : Category.Object D}
    → (p : base x ≡ just x')
    → (q : base y ≡ just y')
    → (r : base z ≡ just z')
    → (f : Category.Arrow C y z)
    → (g : Category.Arrow C x y)
    → Category.ArrowEqual' D
      (map p r (Category.compose C f g))
      (Category.compose D (map q r f) (map p q g))
  map-compose' p q r f g
    = Category.any
    $ map-compose p q r f g

-- ### Conversion

module _
  {C D : Category}
  where

  module FunctorPartial
    (F : Functor C D)
    where

    base
      : Category.Object C
      → Maybe (Category.Object D)
    base x
      = just (Functor.base F x)

    map
      : {x y : Category.Object C}
      → {x' y' : Category.Object D}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow C x y
      → Category.Arrow D x' y'
    map refl refl
      = Functor.map F

    abstract

      map-equal
        : {x y : Category.Object C}
        → {x' y' : Category.Object D}
        → {f₁ f₂ : Category.Arrow C x y}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → Category.ArrowEqual C f₁ f₂
        → Category.ArrowEqual D (map p q f₁) (map p q f₂)
      map-equal refl refl
        = Functor.map-equal F

      map-identity
        : {x' : Category.Object D}
        → (x : Category.Object C)
        → (p : base x ≡ just x')
        → Category.ArrowEqual D
          (map p p (Category.identity C x))
          (Category.identity D x')
      map-identity x refl
        = Functor.map-identity F x

      map-compose
        : {x y z : Category.Object C}
        → {x' y' z' : Category.Object D}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → Category.ArrowEqual D
          (map p r (Category.compose C f g))
          (Category.compose D (map q r f) (map p q g))
      map-compose refl refl refl
        = Functor.map-compose F

  functor-partial
    : Functor C D
    → PartialFunctor C D
  functor-partial F
    = record {FunctorPartial F}

-- ### Compose

module _
  {C D E : Category}
  where

  module PartialFunctorCompose
    (F : PartialFunctor D E)
    (G : PartialFunctor C D)
    where

    base
      : Category.Object C
      → Maybe (Category.Object E)
    base x
      with PartialFunctor.base G x
    ... | nothing
      = nothing
    ... | just x'
      = PartialFunctor.base F x'

    map
      : {x y : Category.Object C}
      → {x' y' : Category.Object E}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow C x y
      → Category.Arrow E x' y'
    map {x = x} {y = y} p' q'
      with PartialFunctor.base G x
      | inspect (PartialFunctor.base G) x
      | PartialFunctor.base G y
      | inspect (PartialFunctor.base G) y
    ... | just _ | [ p ] | just _ | [ q ]
      = PartialFunctor.map F p' q'
      ∘ PartialFunctor.map G p q

    abstract

      map-equal
        : {x y : Category.Object C}
        → {x' y' : Category.Object E}
        → {f₁ f₂ : Category.Arrow C x y}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → Category.ArrowEqual C f₁ f₂
        → Category.ArrowEqual E (map p q f₁) (map p q f₂)
      map-equal {x = x} {y = y} p' q'
        with PartialFunctor.base G x
        | inspect (PartialFunctor.base G) x
        | PartialFunctor.base G y
        | inspect (PartialFunctor.base G) y
      ... | just _ | [ p ] | just _ | [ q ]
        = PartialFunctor.map-equal F p' q'
        ∘ PartialFunctor.map-equal G p q

      map-identity
        : {x' : Category.Object E}
        → (x : Category.Object C)
        → (p : base x ≡ just x')
        → Category.ArrowEqual E
          (map p p (Category.identity C x))
          (Category.identity E x')
      map-identity x p'
        with PartialFunctor.base G x
        | inspect (PartialFunctor.base G) x
      ... | just x' | [ p ]
        = Category.arrow-trans E (PartialFunctor.map-equal F p' p'
          (PartialFunctor.map-identity G x p))
        $ PartialFunctor.map-identity F x' p'
  
      map-compose
        : {x y z : Category.Object C}
        → {x' y' z' : Category.Object E}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → Category.ArrowEqual E
          (map p r (Category.compose C f g))
          (Category.compose E (map q r f) (map p q g))
      map-compose {x = x} {y = y} {z = z} p' q' r' f g
        with PartialFunctor.base G x
        | inspect (PartialFunctor.base G) x
        | PartialFunctor.base G y
        | inspect (PartialFunctor.base G) y
        | PartialFunctor.base G z
        | inspect (PartialFunctor.base G) z
      ... | just _ | [ p ] | just _ | [ q ] | just _ | [ r ]
        = Category.arrow-trans E (PartialFunctor.map-equal F p' r'
          (PartialFunctor.map-compose G p q r f g))
        $ PartialFunctor.map-compose F p' q' r'
          (PartialFunctor.map G q r f)
          (PartialFunctor.map G p q g)

  partial-functor-compose
    : PartialFunctor D E
    → PartialFunctor C D
    → PartialFunctor C E
  partial-functor-compose F G
    = record {PartialFunctorCompose F G}

-- ## PartialFunctorSquare

-- ### Definition

record PartialFunctorSquare
  {C₁ C₂ D₁ D₂ : Category}
  (F : Functor C₁ C₂)
  (G : Functor D₁ D₂)
  (H₁ : PartialFunctor C₁ D₁)
  (H₂ : PartialFunctor C₂ D₂)
  : Set
  where

  field

    base
      : {x₁' : Category.Object D₁}
      → (x₁ : Category.Object C₁)
      → PartialFunctor.base H₁ x₁ ≡ just x₁'
      → PartialFunctor.base H₂ (Functor.base F x₁)
        ≡ just (Functor.base G x₁')

  partial-function
    : PartialFunctionSquare
      (Functor.function F)
      (Functor.function G)
      (PartialFunctor.partial-function H₁)
      (PartialFunctor.partial-function H₂)
  partial-function
    = record
    { base
      = base
    }

  field

    map
      : {x₁ y₁ : Category.Object C₁}
      → {x₁' y₁' : Category.Object D₁}
      → (p₁ : PartialFunctor.base H₁ x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base H₁ y₁ ≡ just y₁')
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Category.ArrowEqual D₂
        (PartialFunctor.map H₂ (base x₁ p₁) (base y₁ q₁) (Functor.map F f₁))
        (Functor.map G (PartialFunctor.map H₁ p₁ q₁ f₁))

  map'
    : {x₁ y₁ : Category.Object C₁}
    → {x₁' y₁' : Category.Object D₁}
    → (p₁ : PartialFunctor.base H₁ x₁ ≡ just x₁')
    → (q₁ : PartialFunctor.base H₁ y₁ ≡ just y₁')
    → (p₂ : PartialFunctor.base H₂ (Functor.base F x₁)
      ≡ just (Functor.base G x₁'))
    → (q₂ : PartialFunctor.base H₂ (Functor.base F y₁)
      ≡ just (Functor.base G y₁'))
    → (f₁ : Category.Arrow C₁ x₁ y₁)
    → Category.ArrowEqual D₂
      (PartialFunctor.map H₂ p₂ q₂ (Functor.map F f₁))
      (Functor.map G (PartialFunctor.map H₁ p₁ q₁ f₁))
  map' {x₁ = x₁} {y₁ = y₁} p₁ q₁ p₂ q₂
    with irrelevant p₂ (base x₁ p₁)
    | irrelevant q₂ (base y₁ q₁)
  ... | refl | refl
    = map p₁ q₁

  map''
    : {x₁ y₁ : Category.Object C₁}
    → {x₂ y₂ : Category.Object C₂}
    → {x₁' y₁' : Category.Object D₁}
    → {x₂' y₂' : Category.Object D₂}
    → (p₁ : PartialFunctor.base H₁ x₁ ≡ just x₁')
    → (q₁ : PartialFunctor.base H₁ y₁ ≡ just y₁')
    → (p₂ : PartialFunctor.base H₂ x₂ ≡ just x₂')
    → (q₂ : PartialFunctor.base H₂ y₂ ≡ just y₂')
    → (f₁ : Category.Arrow C₁ x₁ y₁)
    → {f₂ : Category.Arrow C₂ x₂ y₂}
    → Category.ArrowEqual' C₂ (Functor.map F f₁) f₂
    → Category.ArrowEqual' D₂
      (PartialFunctor.map H₂ p₂ q₂ f₂)
      (Functor.map G (PartialFunctor.map H₁ p₁ q₁ f₁))
  map'' {x₁ = x₁} {y₁ = y₁} p₁ q₁ p₂ q₂ f₁ r
    = Category.arrow-trans' D₂ (Category.arrow-sym' D₂
      (PartialFunctor.map-equal' H₂ (base x₁ p₁) p₂ (base y₁ q₁) q₂ r))
    $ Category.any
    $ map p₁ q₁ f₁

  map-arrow
    : {x₁ y₁ : Category.Object C₁}
    → {x₂ y₂ : Category.Object C₂}
    → {x₁' y₁' : Category.Object D₁}
    → {x₂' y₂' : Category.Object D₂}
    → (p : x₂ ≡ Functor.base F x₁)
    → (q : y₂ ≡ Functor.base F y₁)
    → (p' : x₂' ≡ Functor.base G x₁')
    → (q' : y₂' ≡ Functor.base G y₁')
    → (r₁ : PartialFunctor.base H₁ x₁ ≡ just x₁')
    → (s₁ : PartialFunctor.base H₁ y₁ ≡ just y₁')
    → (r₂ : PartialFunctor.base H₂ x₂ ≡ just x₂')
    → (s₂ : PartialFunctor.base H₂ y₂ ≡ just y₂')
    → (f₁ : Category.Arrow C₁ x₁ y₁)
    → Category.ArrowEqual D₂
      (PartialFunctor.map H₂ r₂ s₂ (Category.arrow C₂ p q (Functor.map F f₁)))
      (Category.arrow D₂ p' q' (Functor.map G (PartialFunctor.map H₁ r₁ s₁ f₁)))
  map-arrow refl refl refl refl
    = map'

-- ### Conversion

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : Functor C₁ D₁}
  {H₂ : Functor C₂ D₂}
  where

  module FunctorSquarePartial
    (s : FunctorSquare F G H₁ H₂)
    where

    base
      : {x₁' : Category.Object D₁}
      → (x₁ : Category.Object C₁)
      → PartialFunctor.base (functor-partial H₁) x₁ ≡ just x₁'
      → PartialFunctor.base (functor-partial H₂) (Functor.base F x₁)
        ≡ just (Functor.base G x₁')
    base x₁ refl
      = sub just (FunctorSquare.base s x₁)

    map'
      : {x₁ y₁ : Category.Object C₁}
      → {x₂ y₂ : Category.Object C₂}
      → {x₁' y₁' : Category.Object D₁}
      → {x₂' y₂' : Category.Object D₂}
      → (p₁ : PartialFunctor.base (functor-partial H₁) x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (functor-partial H₁) y₁ ≡ just y₁')
      → (p₂ : PartialFunctor.base (functor-partial H₂) x₂ ≡ just x₂')
      → (q₂ : PartialFunctor.base (functor-partial H₂) y₂ ≡ just y₂')
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → {f₂ : Category.Arrow C₂ x₂ y₂}
      → Category.ArrowEqual' C₂ (Functor.map F f₁) f₂
      → Category.ArrowEqual' D₂
        (PartialFunctor.map (functor-partial H₂) p₂ q₂ f₂)
        (Functor.map G (PartialFunctor.map (functor-partial H₁) p₁ q₁ f₁))
    map' refl refl refl refl f₁ r
      = Category.arrow-trans' D₂ (Functor.map-equal' H₂
        (Category.arrow-sym' C₂ r))
      $ FunctorSquare.map s f₁

    map
      : {x₁ y₁ : Category.Object C₁}
      → {x₁' y₁' : Category.Object D₁}
      → (p₁ : PartialFunctor.base (functor-partial H₁) x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (functor-partial H₁) y₁ ≡ just y₁')
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Category.ArrowEqual D₂
        (PartialFunctor.map (functor-partial H₂) (base x₁ p₁) (base y₁ q₁)
          (Functor.map F f₁))
        (Functor.map G
          (PartialFunctor.map (functor-partial H₁) p₁ q₁ f₁))
    map {x₁ = x₁} {y₁ = y₁} p₁ q₁ f₁
      = Category.any' D₂
      $ map' p₁ q₁
        (base x₁ p₁)
        (base y₁ q₁) f₁
        (Category.arrow-refl' C₂)

  functor-square-partial
    : FunctorSquare F G H₁ H₂
    → PartialFunctorSquare F G
      (functor-partial H₁)
      (functor-partial H₂)
  functor-square-partial s
    = record {FunctorSquarePartial s}

-- ### Compose

module _
  {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H : Functor E₁ E₂}
  {I₁ : PartialFunctor D₁ E₁}
  {I₂ : PartialFunctor D₂ E₂}
  {J₁ : PartialFunctor C₁ D₁}
  {J₂ : PartialFunctor C₂ D₂}
  where

  module PartialFunctorSquareCompose
    (s : PartialFunctorSquare G H I₁ I₂)
    (t : PartialFunctorSquare F G J₁ J₂)
    where

    base
      : {x₁' : Category.Object E₁}
      → (x₁ : Category.Object C₁)
      → PartialFunctor.base (partial-functor-compose I₁ J₁) x₁ ≡ just x₁'
      → PartialFunctor.base (partial-functor-compose I₂ J₂) (Functor.base F x₁)
        ≡ just (Functor.base H x₁')
    base x₁ _
      with PartialFunctor.base J₁ x₁
      | inspect (PartialFunctor.base J₁) x₁
    ... | just x₁' | [ q₁ ]
      with PartialFunctor.base J₂ (Functor.base F x₁)
      | PartialFunctorSquare.base t x₁ q₁
      | PartialFunctor.base I₁ x₁'
      | inspect (PartialFunctor.base I₁) x₁'
    base _ refl | just x₁' | _ | _ | refl | just _ | [ p₁ ]
      = PartialFunctorSquare.base s x₁' p₁

    map
      : {x₁ y₁ : Category.Object C₁}
      → {x₁' y₁' : Category.Object E₁}
      → (p₁ : PartialFunctor.base (partial-functor-compose I₁ J₁) x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-compose I₁ J₁) y₁ ≡ just y₁')
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → Category.ArrowEqual E₂
        (PartialFunctor.map
          (partial-functor-compose I₂ J₂)
          (base x₁ p₁)
          (base y₁ q₁)
          (Functor.map F f₁))
        (Functor.map H
          (PartialFunctor.map (partial-functor-compose I₁ J₁) p₁ q₁ f₁))
    map {x₁ = x₁} {y₁ = y₁} p₁' q₁' f₁
      with base x₁ p₁'
      | base y₁ q₁'
    ... | p₂' | q₂'
      with PartialFunctor.base J₁ x₁
      | inspect (PartialFunctor.base J₁) x₁
      | PartialFunctor.base J₁ y₁
      | inspect (PartialFunctor.base J₁) y₁
    ... | just _ | [ p₁ ] | just _ | [ q₁ ]
      with PartialFunctor.base J₂ (Functor.base F x₁)
      | inspect (PartialFunctor.base J₂) (Functor.base F x₁)
      | PartialFunctorSquare.base t x₁ p₁
      | PartialFunctor.base J₂ (Functor.base F y₁)
      | inspect (PartialFunctor.base J₂) (Functor.base F y₁)
      | PartialFunctorSquare.base t y₁ q₁
    ... | _ | [ p₂ ] | refl | _ | [ q₂ ] | refl
      = Category.arrow-trans E₂ (PartialFunctor.map-equal I₂ p₂' q₂'
        (PartialFunctorSquare.map' t p₁ q₁ p₂ q₂ f₁))
      $ PartialFunctorSquare.map' s p₁' q₁' p₂' q₂'
        (PartialFunctor.map J₁ p₁ q₁ f₁)

  partial-functor-square-compose
    : PartialFunctorSquare G H I₁ I₂
    → PartialFunctorSquare F G J₁ J₂
    → PartialFunctorSquare F H
      (partial-functor-compose I₁ J₁)
      (partial-functor-compose I₂ J₂)
  partial-functor-square-compose s t
    = record {PartialFunctorSquareCompose s t}

