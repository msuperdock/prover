module Prover.Category.Partial where

open import Prover.Category
  using (Category; Functor)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

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

    map-identity
      : {x' : Category.Object D}
      → (x : Category.Object C)
      → (p : base x ≡ just x')
      → map p p (Category.identity C x)
        ≡ Category.identity D x'

    map-compose
      : {x y z : Category.Object C}
      → {x' y' z' : Category.Object D}
      → (p : base x ≡ just x')
      → (q : base y ≡ just y')
      → (r : base z ≡ just z')
      → (f : Category.Arrow C y z)
      → (g : Category.Arrow C x y)
      → map p r (Category.compose C f g)
        ≡ Category.compose D (map q r f) (map p q g)

  map-eq
    : {x₁ x₂ y₁ y₂ : Category.Object C}
    → {x' y' : Category.Object D}
    → {f₁ : Category.Arrow C x₁ y₁}
    → {f₂ : Category.Arrow C x₂ y₂}
    → (p₁ : base x₁ ≡ just x')
    → (p₂ : base x₂ ≡ just x')
    → (q₁ : base y₁ ≡ just y')
    → (q₂ : base y₂ ≡ just y')
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → f₁ ≅ f₂
    → map p₁ q₁ f₁ ≡ map p₂ q₂ f₂
  map-eq p₁ p₂ q₁ q₂ refl refl refl
    with irrelevant p₁ p₂
    | irrelevant q₁ q₂
  ... | refl | refl
    = refl

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

      map-identity
        : {x' : Category.Object E}
        → (x : Category.Object C)
        → (p : base x ≡ just x')
        → map p p (Category.identity C x) ≡ Category.identity E x'
      map-identity x p'
        with PartialFunctor.base G x
        | inspect (PartialFunctor.base G) x
      ... | just x' | [ p ]
        with PartialFunctor.map G p p (Category.identity C x)
        | PartialFunctor.map-identity G x p
      ... | _ | refl
        = PartialFunctor.map-identity F x' p'
  
      map-compose
        : {x y z : Category.Object C}
        → {x' y' z' : Category.Object E}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → map p r (Category.compose C f g)
          ≡ Category.compose E (map q r f) (map p q g)
      map-compose {x = x} {y = y} {z = z} p' q' r' f g
        with PartialFunctor.base G x
        | inspect (PartialFunctor.base G) x
        | PartialFunctor.base G y
        | inspect (PartialFunctor.base G) y
        | PartialFunctor.base G z
        | inspect (PartialFunctor.base G) z
      ... | just _ | [ p ] | just _ | [ q ] | just _ | [ r ]
        with PartialFunctor.map G p r (Category.compose C f g)
        | PartialFunctor.map-compose G p q r f g
      ... | _ | refl
        = PartialFunctor.map-compose F p' q' r'
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

    map
      : {x₁ y₁ : Category.Object C₁}
      → {x₁' y₁' : Category.Object D₁}
      → (p₁ : PartialFunctor.base H₁ x₁ ≡ just x₁')
      → (q₁ : PartialFunctor.base H₁ y₁ ≡ just y₁')
      → (f₁ : Category.Arrow C₁ x₁ y₁)
      → PartialFunctor.map H₂ (base x₁ p₁) (base y₁ q₁) (Functor.map F f₁)
        ≡ Functor.map G (PartialFunctor.map H₁ p₁ q₁ f₁)

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
    → PartialFunctor.map H₂ p₂ q₂ (Functor.map F f₁)
      ≡ Functor.map G (PartialFunctor.map H₁ p₁ q₁ f₁)
  map' {x₁ = x₁} {y₁ = y₁} p₁ q₁ p₂ q₂
    with irrelevant p₂ (base x₁ p₁)
    | irrelevant q₂ (base y₁ q₁)
  ... | refl | refl
    = map p₁ q₁

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
    → PartialFunctor.map H₂ r₂ s₂ (Category.arrow C₂ p q (Functor.map F f₁))
      ≡ Category.arrow D₂ p' q' (Functor.map G (PartialFunctor.map H₁ r₁ s₁ f₁))
  map-arrow refl refl refl refl
    = map'

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
      → PartialFunctor.map
        (partial-functor-compose I₂ J₂)
        (base x₁ p₁)
        (base y₁ q₁)
        (Functor.map F f₁)
      ≡ Functor.map H
        (PartialFunctor.map (partial-functor-compose I₁ J₁) p₁ q₁ f₁)
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
      = trans
        (sub (PartialFunctor.map I₂ p₂' q₂')
          (PartialFunctorSquare.map' t p₁ q₁ p₂ q₂ f₁))
        (PartialFunctorSquare.map' s p₁' q₁' p₂' q₂'
          (PartialFunctor.map J₁ p₁ q₁ f₁))

  partial-functor-square-compose
    : PartialFunctorSquare G H I₁ I₂
    → PartialFunctorSquare F G J₁ J₂
    → PartialFunctorSquare F H
      (partial-functor-compose I₁ J₁)
      (partial-functor-compose I₂ J₂)
  partial-functor-square-compose s t
    = record {PartialFunctorSquareCompose s t}

-- ## PartialFunctorSquare'

module _PartialFunctorSquare' where

  data PartialFunctorSquare'
    : {C₁ C₂ D₁ D₂ D₃ : Category}
    → Functor C₁ C₂
    → Functor D₁ D₃
    → PartialFunctor C₁ D₁
    → PartialFunctor C₂ D₂
    → Set
    where
  
    partial-functor-square'
      : {C₁ C₂ D₁ D₂ : Category}
      → {F : Functor C₁ C₂}
      → {G : Functor D₁ D₂}
      → {H₁ : PartialFunctor C₁ D₁}
      → {H₂ : PartialFunctor C₂ D₂}
      → PartialFunctorSquare F G H₁ H₂
      → PartialFunctorSquare' F G H₁ H₂

PartialFunctorSquare'
  : {C₁ C₂ D₁ D₂ D₃ : Category}
  → Functor C₁ C₂
  → Functor D₁ D₃
  → PartialFunctor C₁ D₁
  → PartialFunctor C₂ D₂
  → Set
PartialFunctorSquare'
  = _PartialFunctorSquare'.PartialFunctorSquare'
 
open _PartialFunctorSquare'.PartialFunctorSquare' public

module PartialFunctorSquare' where

  base
    : {C₁ C₂ D₁ D₂ D₃ : Category}
    → {F : Functor C₁ C₂}
    → {G : Functor D₁ D₃}
    → {H₁ : PartialFunctor C₁ D₁}
    → {H₂ : PartialFunctor C₂ D₂}
    → PartialFunctorSquare' F G H₁ H₂
    → {x₁' : Category.Object D₁}
    → (x₁ : Category.Object C₁)
    → PartialFunctor.base H₁ x₁ ≡ just x₁'
    → Equal'
      (Maybe (Category.Object D₂))
      (Maybe (Category.Object D₃))
      (PartialFunctor.base H₂ (Functor.base F x₁))
      (just (Functor.base G x₁'))
  base (partial-functor-square' s)
    = PartialFunctorSquare.base s
  
  map-eq
    : {C₁ C₂ D₁ D₂ D₃ : Category}
    → {F : Functor C₁ C₂}
    → {G : Functor D₁ D₃}
    → {H₁ : PartialFunctor C₁ D₁}
    → {H₂ : PartialFunctor C₂ D₂}
    → PartialFunctorSquare' F G H₁ H₂
    → {x₁ y₁ : Category.Object C₁}
    → {x₁' y₁' : Category.Object D₁}
    → {x₂' y₂' : Category.Object D₂}
    → (p₁ : PartialFunctor.base H₁ x₁ ≡ just x₁')
    → (q₁ : PartialFunctor.base H₁ y₁ ≡ just y₁')
    → (p₂ : PartialFunctor.base H₂ (Functor.base F x₁) ≡ just x₂')
    → (q₂ : PartialFunctor.base H₂ (Functor.base F y₁) ≡ just y₂')
    → (f₁ : Category.Arrow C₁ x₁ y₁)
    → Functor.base G x₁' ≅ x₂'
    → Functor.base G y₁' ≅ y₂'
    → PartialFunctor.map H₂ p₂ q₂ (Functor.map F f₁)
      ≅ Functor.map G (PartialFunctor.map H₁ p₁ q₁ f₁)
  map-eq (partial-functor-square' s) p₁ q₁ p₂ q₂ f₁ refl refl
    = PartialFunctorSquare.map' s p₁ q₁ p₂ q₂ f₁

