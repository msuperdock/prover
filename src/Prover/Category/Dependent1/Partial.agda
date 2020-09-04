module Prover.Category.Dependent1.Partial where

open import Prover.Category
  using (Category; FunctorEqual)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare; PartialFunctorSquare')
open import Prover.Prelude

-- ## Dependent₁PartialFunctor

record Dependent₁PartialFunctor
  {C : Category}
  (C' D' : Dependent₁Category C)
  : Set
  where

  no-eta-equality

  field

    partial-functor
      : (x : Category.Object C)
      → PartialFunctor
        (Dependent₁Category.category C' x)
        (Dependent₁Category.category D' x)

  base
    : (x : Category.Object C)
    → Dependent₁Category.Object C' x
    → Maybe (Dependent₁Category.Object D' x)
  base x
    = PartialFunctor.base
      (partial-functor x)

  map
    : (x : Category.Object C)
    → {x' y' : Dependent₁Category.Object C' x}
    → {x'' y'' : Dependent₁Category.Object D' x}
    → base x x' ≡ just x''
    → base x y' ≡ just y''
    → Dependent₁Category.Arrow C' x x' y'
    → Dependent₁Category.Arrow D' x x'' y''
  map x
    = PartialFunctor.map
      (partial-functor x)

  map-identity
    : (x : Category.Object C)
    → {x'' : Dependent₁Category.Object D' x}
    → (x' : Dependent₁Category.Object C' x)
    → (p : base x x' ≡ just x'')
    → map x p p (Dependent₁Category.identity C' x x')
      ≡ Dependent₁Category.identity D' x x''
  map-identity x
    = PartialFunctor.map-identity
      (partial-functor x)

  map-compose
    : (x : Category.Object C)
    → {x' y' z' : Dependent₁Category.Object C' x}
    → {x'' y'' z'' : Dependent₁Category.Object D' x}
    → (p : base x x' ≡ just x'')
    → (q : base x y' ≡ just y'')
    → (r : base x z' ≡ just z'')
    → (f' : Dependent₁Category.Arrow C' x y' z')
    → (g' : Dependent₁Category.Arrow C' x x' y')
    → map x p r (Dependent₁Category.compose C' x f' g')
      ≡ Dependent₁Category.compose D' x (map x q r f') (map x p q g')
  map-compose x
    = PartialFunctor.map-compose
      (partial-functor x)

  field

    partial-functor-square
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → PartialFunctorSquare
        (Dependent₁Category.functor C' f)
        (Dependent₁Category.functor D' f)
        (partial-functor x)
        (partial-functor y)

  base-commutative
    : {x y : Category.Object C}
    → {x'' : Dependent₁Category.Object D' x}
    → (f : Category.Arrow C x y)
    → (x' : Dependent₁Category.Object C' x)
    → base x x' ≡ just x''
    → base y (Dependent₁Category.base C' f x')
      ≡ just (Dependent₁Category.base D' f x'')
  base-commutative f
    = PartialFunctorSquare.base
      (partial-functor-square f)

  map-commutative
    : {x y : Category.Object C}
    → {x' y' : Dependent₁Category.Object C' x}
    → {x'' y'' : Dependent₁Category.Object D' x}
    → (f : Category.Arrow C x y)
    → (p : PartialFunctor.base (partial-functor x) x' ≡ just x'')
    → (q : PartialFunctor.base (partial-functor x) y' ≡ just y'')
    → (f' : Dependent₁Category.Arrow C' x x' y')
    → map y
      (base-commutative f x' p)
      (base-commutative f y' q)
      (Dependent₁Category.map C' f f')
    ≡ Dependent₁Category.map D' f (map x p q f')
  map-commutative f
    = PartialFunctorSquare.map
      (partial-functor-square f)

-- ## Dependent₁PartialFunctorSquare

record Dependent₁PartialFunctorSquare
  {C₁ C₂ : Category}
  {C₁' D₁' : Dependent₁Category C₁}
  {C₂' D₂' : Dependent₁Category C₂}
  (F : Dependent₁Functor C₁' C₂')
  (G : Dependent₁Functor D₁' D₂')
  (H₁ : Dependent₁PartialFunctor C₁' D₁')
  (H₂ : Dependent₁PartialFunctor C₂' D₂')
  : Set
  where

  field

    functor
      : FunctorEqual
        (Dependent₁Functor.functor F)
        (Dependent₁Functor.functor G)
    
  open FunctorEqual functor public

  field

    partial-functor
      : (x₁ : Category.Object C₁)
      → PartialFunctorSquare'
        (Dependent₁Functor.functor' F x₁)
        (Dependent₁Functor.functor' G x₁)
        (Dependent₁PartialFunctor.partial-functor H₁ x₁)
        (Dependent₁PartialFunctor.partial-functor H₂
          (Dependent₁Functor.base F x₁))

  base'
    : (x₁ : Category.Object C₁)
    → {x₁'' : Dependent₁Category.Object D₁' x₁}
    → (x₁' : Dependent₁Category.Object C₁' x₁)
    → Dependent₁PartialFunctor.base H₁ x₁ x₁' ≡ just x₁''
    → Equal'
      (Maybe (Dependent₁Category.Object D₂' (Dependent₁Functor.base F x₁)))
      (Maybe (Dependent₁Category.Object D₂' (Dependent₁Functor.base G x₁)))
      (Dependent₁PartialFunctor.base H₂
        (Dependent₁Functor.base F x₁)
        (Dependent₁Functor.base' F x₁ x₁'))
      (just (Dependent₁Functor.base' G x₁ x₁''))
  base' x₁
    = PartialFunctorSquare'.base
      (partial-functor x₁)

  map-eq'
    : (x₁ : Category.Object C₁)
    → {x₁' y₁' : Dependent₁Category.Object C₁' x₁}
    → {x₁'' y₁'' : Dependent₁Category.Object D₁' x₁}
    → {x₂'' y₂'' : Dependent₁Category.Object D₂' (Dependent₁Functor.base F x₁)}
    → (p₁ : Dependent₁PartialFunctor.base H₁ x₁ x₁' ≡ just x₁'')
    → (q₁ : Dependent₁PartialFunctor.base H₁ x₁ y₁' ≡ just y₁'')
    → (p₂ : Dependent₁PartialFunctor.base H₂
      (Dependent₁Functor.base F x₁)
      (Dependent₁Functor.base' F x₁ x₁')
      ≡ just x₂'')
    → (q₂ : Dependent₁PartialFunctor.base H₂
      (Dependent₁Functor.base F x₁)
      (Dependent₁Functor.base' F x₁ y₁')
      ≡ just y₂'')
    → (f₁ : Dependent₁Category.Arrow C₁' x₁ x₁' y₁')
    → Dependent₁Functor.base' G x₁ x₁'' ≅ x₂''
    → Dependent₁Functor.base' G x₁ y₁'' ≅ y₂''
    → Dependent₁PartialFunctor.map H₂
      (Dependent₁Functor.base F x₁) p₂ q₂
      (Dependent₁Functor.map' F x₁ f₁)
    ≅ Dependent₁Functor.map' G x₁
      (Dependent₁PartialFunctor.map H₁ x₁ p₁ q₁ f₁)
  map-eq' x₁
    = PartialFunctorSquare'.map-eq
      (partial-functor x₁)

