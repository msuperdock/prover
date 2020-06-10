module Prover.Category.Partial where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; Functor; FunctorEqual)
open import Prover.Prelude

-- ## PartialFunctor

-- ### Definition

record PartialFunctor
  (C D : Category)
  : Set
  where

  field

    base
      : Category.Object C
      → Maybe (Category.Object D)

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

  map-eq
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
  map-eq {x₁ = x₁} {y₁ = y₁} p₁ q₁ p₂ q₂
    with irrelevant p₂ (base x₁ p₁)
    | irrelevant q₂ (base y₁ q₁)
  ... | refl | refl
    = map p₁ q₁

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
    ... | just x₁' | [ p₁ ] | just y₁' | [ q₁ ]
      with PartialFunctor.base J₂ (Functor.base F x₁)
      | inspect (PartialFunctor.base J₂) (Functor.base F x₁)
      | PartialFunctorSquare.base t x₁ p₁
      | PartialFunctor.base J₂ (Functor.base F y₁)
      | inspect (PartialFunctor.base J₂) (Functor.base F y₁)
      | PartialFunctorSquare.base t y₁ q₁
    ... | _ | [ p₂ ] | refl | _ | [ q₂ ] | refl
      = trans
        (sub (PartialFunctor.map I₂ p₂' q₂')
          (PartialFunctorSquare.map-eq t p₁ q₁ p₂ q₂ f₁))
        (PartialFunctorSquare.map-eq s p₁' q₁' p₂' q₂'
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
    → Equal
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
    = PartialFunctorSquare.map-eq s p₁ q₁ p₂ q₂ f₁

-- ## PartialDependentFunctor

record PartialDependentFunctor
  {C : Category}
  (C' D' : DependentCategory C)
  : Set
  where

  no-eta-equality

  field

    partial-functor
      : (x : Category.Object C)
      → PartialFunctor
        (DependentCategory.category C' x)
        (DependentCategory.category D' x)

  base
    : (x : Category.Object C)
    → DependentCategory.Object C' x
    → Maybe (DependentCategory.Object D' x)
  base x
    = PartialFunctor.base
      (partial-functor x)

  map
    : (x : Category.Object C)
    → {x' y' : DependentCategory.Object C' x}
    → {x'' y'' : DependentCategory.Object D' x}
    → base x x' ≡ just x''
    → base x y' ≡ just y''
    → DependentCategory.Arrow C' x x' y'
    → DependentCategory.Arrow D' x x'' y''
  map x
    = PartialFunctor.map
      (partial-functor x)

  map-identity
    : (x : Category.Object C)
    → {x'' : DependentCategory.Object D' x}
    → (x' : DependentCategory.Object C' x)
    → (p : base x x' ≡ just x'')
    → map x p p (DependentCategory.identity C' x x')
      ≡ DependentCategory.identity D' x x''
  map-identity x
    = PartialFunctor.map-identity
      (partial-functor x)

  map-compose
    : (x : Category.Object C)
    → {x' y' z' : DependentCategory.Object C' x}
    → {x'' y'' z'' : DependentCategory.Object D' x}
    → (p : base x x' ≡ just x'')
    → (q : base x y' ≡ just y'')
    → (r : base x z' ≡ just z'')
    → (f' : DependentCategory.Arrow C' x y' z')
    → (g' : DependentCategory.Arrow C' x x' y')
    → map x p r (DependentCategory.compose C' x f' g')
      ≡ DependentCategory.compose D' x (map x q r f') (map x p q g')
  map-compose x
    = PartialFunctor.map-compose
      (partial-functor x)

  field

    partial-functor-square
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → PartialFunctorSquare
        (DependentCategory.functor C' f)
        (DependentCategory.functor D' f)
        (partial-functor x)
        (partial-functor y)

  base-commutative
    : {x y : Category.Object C}
    → {x'' : DependentCategory.Object D' x}
    → (f : Category.Arrow C x y)
    → (x' : DependentCategory.Object C' x)
    → base x x' ≡ just x''
    → base y (DependentCategory.base C' f x')
      ≡ just (DependentCategory.base D' f x'')
  base-commutative f
    = PartialFunctorSquare.base
      (partial-functor-square f)

  map-commutative
    : {x y : Category.Object C}
    → {x' y' : DependentCategory.Object C' x}
    → {x'' y'' : DependentCategory.Object D' x}
    → (f : Category.Arrow C x y)
    → (p : PartialFunctor.base (partial-functor x) x' ≡ just x'')
    → (q : PartialFunctor.base (partial-functor x) y' ≡ just y'')
    → (f' : DependentCategory.Arrow C' x x' y')
    → map y
      (base-commutative f x' p)
      (base-commutative f y' q)
      (DependentCategory.map C' f f')
    ≡ DependentCategory.map D' f (map x p q f')
  map-commutative f
    = PartialFunctorSquare.map
      (partial-functor-square f)

-- ## PartialDependentFunctorSquare

record PartialDependentFunctorSquare
  {C₁ C₂ : Category}
  {C₁' D₁' : DependentCategory C₁}
  {C₂' D₂' : DependentCategory C₂}
  (F : DependentFunctor C₁' C₂')
  (G : DependentFunctor D₁' D₂')
  (H₁ : PartialDependentFunctor C₁' D₁')
  (H₂ : PartialDependentFunctor C₂' D₂')
  : Set
  where

  field

    functor
      : FunctorEqual
        (DependentFunctor.functor F)
        (DependentFunctor.functor G)
    
  open FunctorEqual functor public

  field

    partial-functor
      : (x₁ : Category.Object C₁)
      → PartialFunctorSquare'
        (DependentFunctor.functor' F x₁)
        (DependentFunctor.functor' G x₁)
        (PartialDependentFunctor.partial-functor H₁ x₁)
        (PartialDependentFunctor.partial-functor H₂
          (DependentFunctor.base F x₁))

  base'
    : (x₁ : Category.Object C₁)
    → {x₁'' : DependentCategory.Object D₁' x₁}
    → (x₁' : DependentCategory.Object C₁' x₁)
    → PartialDependentFunctor.base H₁ x₁ x₁' ≡ just x₁''
    → Equal
      (Maybe (DependentCategory.Object D₂' (DependentFunctor.base F x₁)))
      (Maybe (DependentCategory.Object D₂' (DependentFunctor.base G x₁)))
      (PartialDependentFunctor.base H₂
        (DependentFunctor.base F x₁)
        (DependentFunctor.base' F x₁ x₁'))
      (just (DependentFunctor.base' G x₁ x₁''))
  base' x₁
    = PartialFunctorSquare'.base
      (partial-functor x₁)

  map-eq'
    : (x₁ : Category.Object C₁)
    → {x₁' y₁' : DependentCategory.Object C₁' x₁}
    → {x₁'' y₁'' : DependentCategory.Object D₁' x₁}
    → {x₂'' y₂'' : DependentCategory.Object D₂' (DependentFunctor.base F x₁)}
    → (p₁ : PartialDependentFunctor.base H₁ x₁ x₁' ≡ just x₁'')
    → (q₁ : PartialDependentFunctor.base H₁ x₁ y₁' ≡ just y₁'')
    → (p₂ : PartialDependentFunctor.base H₂
      (DependentFunctor.base F x₁)
      (DependentFunctor.base' F x₁ x₁')
      ≡ just x₂'')
    → (q₂ : PartialDependentFunctor.base H₂
      (DependentFunctor.base F x₁)
      (DependentFunctor.base' F x₁ y₁')
      ≡ just y₂'')
    → (f₁ : DependentCategory.Arrow C₁' x₁ x₁' y₁')
    → DependentFunctor.base' G x₁ x₁'' ≅ x₂''
    → DependentFunctor.base' G x₁ y₁'' ≅ y₂''
    → PartialDependentFunctor.map H₂
      (DependentFunctor.base F x₁) p₂ q₂
      (DependentFunctor.map' F x₁ f₁)
    ≅ DependentFunctor.map' G x₁
      (PartialDependentFunctor.map H₁ x₁ p₁ q₁ f₁)
  map-eq' x₁
    = PartialFunctorSquare'.map-eq
      (partial-functor x₁)

