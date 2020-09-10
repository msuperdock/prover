module Prover.Category.Partial.Setoid where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Setoid
  using (module CategorySetoid; SetoidCategory; SetoidFunctor; category-setoid;
    functor-setoid)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialSetoidFunctor

-- ### Definition

record PartialSetoidFunctor
  (C D : SetoidCategory)
  : Set
  where

  no-eta-equality

  field

    base
      : SetoidCategory.Object C
      → Maybe (SetoidCategory.Object D)

  partial-function
    : PartialFunction
      (SetoidCategory.Object C)
      (SetoidCategory.Object D)
  partial-function
    = record
    { base
      = base
    }

  field

    map
      : {x y : SetoidCategory.Object C}
      → {x' y' : SetoidCategory.Object D}
      → base x ≡ just x'
      → base y ≡ just y'
      → SetoidCategory.Arrow C x y
      → SetoidCategory.Arrow D x' y'

    map-eq
      : {x y : SetoidCategory.Object C}
      → {x' y' : SetoidCategory.Object D}
      → {f₁ f₂ : SetoidCategory.Arrow C x y}
      → (p : base x ≡ just x')
      → (q : base y ≡ just y')
      → SetoidCategory.ArrowEqual C f₁ f₂
      → SetoidCategory.ArrowEqual D (map p q f₁) (map p q f₂)

    map-identity
      : {x' : SetoidCategory.Object D}
      → (x : SetoidCategory.Object C)
      → (p : base x ≡ just x')
      → SetoidCategory.ArrowEqual D
        (map p p (SetoidCategory.identity C x))
        (SetoidCategory.identity D x')

    map-compose
      : {x y z : SetoidCategory.Object C}
      → {x' y' z' : SetoidCategory.Object D}
      → (p : base x ≡ just x')
      → (q : base y ≡ just y')
      → (r : base z ≡ just z')
      → (f : SetoidCategory.Arrow C y z)
      → (g : SetoidCategory.Arrow C x y)
      → SetoidCategory.ArrowEqual D
        (map p r (SetoidCategory.compose C f g))
        (SetoidCategory.compose D (map q r f) (map p q g))

-- ### Conversion

module _
  {C D : SetoidCategory}
  where

  module PartialFunctorSetoid
    (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    (D' : SetoidCategory.Object D → SetoidCategory.Object D → Set)
    (F : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    (G : (x y : SetoidCategory.Object D)
      → SetoidIsomorphism (D' x y) (SetoidCategory.ArrowSetoid D x y))
    (H : PartialSetoidFunctor C D)
    where

    open CategorySetoid
      using (from; from-eq; to; to-from)

    base
      : Category.Object (category-setoid C C' F)
      → Maybe (Category.Object (category-setoid D D' G))
    base
      = PartialSetoidFunctor.base H

    map
      : {x y : Category.Object (category-setoid C C' F)}
      → {x' y' : Category.Object (category-setoid D D' G)}
      → base x ≡ just x'
      → base y ≡ just y'
      → Category.Arrow (category-setoid C C' F) x y
      → Category.Arrow (category-setoid D D' G) x' y'
    map p q
      = from D D' G
      ∘ PartialSetoidFunctor.map H p q
      ∘ to C C' F

    abstract

      map-identity
        : {x' : Category.Object (category-setoid D D' G)}
        → (x : Category.Object (category-setoid C C' F))
        → (p : base x ≡ just x')
        → map p p (Category.identity (category-setoid C C' F) x)
          ≡ Category.identity (category-setoid D D' G) x'
      map-identity x p
        = trans (from-eq D D' G (PartialSetoidFunctor.map-eq H p p
          (to-from C C' F (SetoidCategory.identity C x))))
        $ from-eq D D' G (PartialSetoidFunctor.map-identity H x p)

      map-compose
        : {x y z : Category.Object (category-setoid C C' F)}
        → {x' y' z' : Category.Object (category-setoid D D' G)}
        → (p : base x ≡ just x')
        → (q : base y ≡ just y')
        → (r : base z ≡ just z')
        → (f : Category.Arrow (category-setoid C C' F) y z)
        → (g : Category.Arrow (category-setoid C C' F) x y)
        → map p r (Category.compose (category-setoid C C' F) f g)
          ≡ Category.compose (category-setoid D D' G) (map q r f) (map p q g)
      map-compose p q r f g
        = trans (from-eq D D' G (PartialSetoidFunctor.map-eq H p r
          (to-from C C' F (SetoidCategory.compose C (to C C' F f) (to C C' F g)))))
        $ trans (from-eq D D' G (PartialSetoidFunctor.map-compose H p q r
          (to C C' F f) (to C C' F g)))
        $ sym (from-eq D D' G (SetoidCategory.compose-eq D
          (to-from D D' G (PartialSetoidFunctor.map H q r (to C C' F f)))
          (to-from D D' G (PartialSetoidFunctor.map H p q (to C C' F g)))))

  partial-functor-setoid
    : (C' : SetoidCategory.Object C → SetoidCategory.Object C → Set)
    → (D' : SetoidCategory.Object D → SetoidCategory.Object D → Set)
    → (F : (x y : SetoidCategory.Object C)
      → SetoidIsomorphism (C' x y) (SetoidCategory.ArrowSetoid C x y))
    → (G : (x y : SetoidCategory.Object D)
      → SetoidIsomorphism (D' x y) (SetoidCategory.ArrowSetoid D x y))
    → PartialSetoidFunctor C D
    → PartialFunctor
      (category-setoid C C' F)
      (category-setoid D D' G)
  partial-functor-setoid A B F G H
    = record {PartialFunctorSetoid A B F G H}

-- ## PartialSetoidFunctorSquare

-- ### Definition

record PartialSetoidFunctorSquare
  {C₁ C₂ D₁ D₂ : SetoidCategory}
  (F : SetoidFunctor C₁ C₂)
  (G : SetoidFunctor D₁ D₂)
  (H₁ : PartialSetoidFunctor C₁ D₁)
  (H₂ : PartialSetoidFunctor C₂ D₂)
  : Set
  where

  field

    base
      : {x₁' : SetoidCategory.Object D₁}
      → (x₁ : SetoidCategory.Object C₁)
      → PartialSetoidFunctor.base H₁ x₁ ≡ just x₁'
      → PartialSetoidFunctor.base H₂ (SetoidFunctor.base F x₁)
        ≡ just (SetoidFunctor.base G x₁')

    map
      : {x₁ y₁ : SetoidCategory.Object C₁}
      → {x₁' y₁' : SetoidCategory.Object D₁}
      → (p₁ : PartialSetoidFunctor.base H₁ x₁ ≡ just x₁')
      → (q₁ : PartialSetoidFunctor.base H₁ y₁ ≡ just y₁')
      → (f₁ : SetoidCategory.Arrow C₁ x₁ y₁)
      → SetoidCategory.ArrowEqual D₂
        (PartialSetoidFunctor.map H₂ (base x₁ p₁) (base y₁ q₁)
          (SetoidFunctor.map F f₁))
        (SetoidFunctor.map G
          (PartialSetoidFunctor.map H₁ p₁ q₁ f₁))

-- ### Conversion

module _
  {C₁ C₂ D₁ D₂ : SetoidCategory}
  {F : SetoidFunctor C₁ C₂}
  {G : SetoidFunctor D₁ D₂}
  {H₁ : PartialSetoidFunctor C₁ D₁}
  {H₂ : PartialSetoidFunctor C₂ D₂}
  where

  module PartialFunctorSquareSetoid
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
    (s : PartialSetoidFunctorSquare F G H₁ H₂)
    where

    open CategorySetoid
      using (from-eq; to; to-from)

    base
      : {x₁' : Category.Object (category-setoid D₁ D₁' J₁)}
      → (x₁ : Category.Object (category-setoid C₁ C₁' I₁))
      → PartialFunctor.base (partial-functor-setoid C₁' D₁' I₁ J₁ H₁) x₁
        ≡ just x₁'
      → PartialFunctor.base (partial-functor-setoid C₂' D₂' I₂ J₂ H₂)
        (Functor.base (functor-setoid C₁' C₂' I₁ I₂ F) x₁)
      ≡ just (Functor.base (functor-setoid D₁' D₂' J₁ J₂ G) x₁')
    base
      = PartialSetoidFunctorSquare.base s

    map
      : {x₁ y₁ : Category.Object (category-setoid C₁ C₁' I₁)}
      → {x₁' y₁' : Category.Object (category-setoid D₁ D₁' J₁)}
      → (p₁ : PartialFunctor.base (partial-functor-setoid C₁' D₁' I₁ J₁ H₁) x₁
        ≡ just x₁')
      → (q₁ : PartialFunctor.base (partial-functor-setoid C₁' D₁' I₁ J₁ H₁) y₁
        ≡ just y₁')
      → (f₁ : Category.Arrow (category-setoid C₁ C₁' I₁) x₁ y₁)
      → PartialFunctor.map (partial-functor-setoid C₂' D₂' I₂ J₂ H₂)
        (base x₁ p₁)
        (base y₁ q₁)
        (Functor.map (functor-setoid C₁' C₂' I₁ I₂ F) f₁)
      ≡ Functor.map (functor-setoid D₁' D₂' J₁ J₂ G)
        (PartialFunctor.map (partial-functor-setoid C₁' D₁' I₁ J₁ H₁) p₁ q₁ f₁)
    map {x₁ = x₁} {y₁ = y₁} p₁ q₁ f₁
      = trans (from-eq D₂ D₂' J₂ (PartialSetoidFunctor.map-eq H₂
        (PartialSetoidFunctorSquare.base s x₁ p₁)
        (PartialSetoidFunctorSquare.base s y₁ q₁)
        (to-from C₂ C₂' I₂ (SetoidFunctor.map F (to C₁ C₁' I₁ f₁)))))
      $ trans (from-eq D₂ D₂' J₂ (PartialSetoidFunctorSquare.map s p₁ q₁
        (to C₁ C₁' I₁ f₁)))
      $ sym (from-eq D₂ D₂' J₂ (SetoidFunctor.map-eq G
        (to-from D₁ D₁' J₁ (PartialSetoidFunctor.map H₁ p₁ q₁
          (to C₁ C₁' I₁ f₁)))))

  partial-functor-square-setoid
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
    → PartialSetoidFunctorSquare F G H₁ H₂
    → PartialFunctorSquare
      (functor-setoid C₁' C₂' I₁ I₂ F)
      (functor-setoid D₁' D₂' J₁ J₂ G)
      (partial-functor-setoid C₁' D₁' I₁ J₁ H₁)
      (partial-functor-setoid C₂' D₂' I₂ J₂ H₂)
  partial-functor-square-setoid C₁' C₂' D₁' D₂' I₁ I₂ J₁ J₂ s
    = record {PartialFunctorSquareSetoid C₁' C₂' D₁' D₂' I₁ I₂ J₁ J₂ s}

