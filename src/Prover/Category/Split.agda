module Prover.Category.Split where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; DependentFunctorSquare;
    Functor; FunctorEqual; FunctorSquare; functor-compose'; functor-identity';
    functor-square-compose; functor-square-identity-eq; functor-sym)
open import Prover.Category.Partial
  using (PartialDependentFunctor; PartialDependentFunctorSquare; PartialFunctor;
    PartialFunctorSquare; PartialFunctorSquare'; partial-functor-compose;
    partial-functor-square'; partial-functor-square-compose)
open import Prover.Category.Simple
  using (PartialRetraction)
open import Prover.Category.Weak
  using (WeakFunctor; WeakFunctorSquare)
open import Prover.Prelude

-- ## SplitFunctor

-- ### Definition

record SplitFunctor
  (C D : Category)
  : Set
  where

  no-eta-equality

  field

    partial-functor
      : PartialFunctor C D

  open PartialFunctor partial-functor public

  field

    functor
      : Functor D C

  open Functor functor public using () renaming
    ( base
      to unbase
    ; map
      to unmap
    ; map-identity
      to unmap-identity
    ; map-compose
      to unmap-compose
    ; map-compose-eq
      to unmap-compose-eq
    )

  field

    base-unbase
      : (x' : Category.Object D)
      → base (unbase x') ≡ just x'

    map-unmap
      : {x' y' : Category.Object D}
      → (f' : Category.Arrow D x' y')
      → map (base-unbase x') (base-unbase y') (unmap f') ≡ f'

    normalize-arrow
      : {x' : Category.Object D}
      → (x : Category.Object C)
      → base x ≡ just x'
      → Category.Arrow C x (unbase x')

    normalize-valid
      : {x' : Category.Object D}
      → (x : Category.Object C)
      → (p : base x ≡ just x')
      → map p (base-unbase x') (normalize-arrow x p) ≡ Category.identity D x'

  partial-retraction
    : PartialRetraction
      (Category.Object C)
      (Category.Object D)
  partial-retraction
    = record
      { to
        = base
      ; from
        = unbase
      ; to-from
        = base-unbase
      }

-- ### Compose

module _
  {C D E : Category}
  where

  module SplitFunctorCompose
    (F : SplitFunctor D E)
    (G : SplitFunctor C D)
    where

    partial-functor
      : PartialFunctor C E
    partial-functor
      = partial-functor-compose
        (SplitFunctor.partial-functor F)
        (SplitFunctor.partial-functor G)
  
    open PartialFunctor partial-functor

    functor
      : Functor E C
    functor
      = functor-compose'
        (SplitFunctor.functor G)
        (SplitFunctor.functor F)
  
    open Functor functor using () renaming
      ( base
        to unbase
      ; map
        to unmap
      ; map-identity
        to unmap-identity
      ; map-compose
        to unmap-compose
      )

    abstract

      base-unbase
        : (x' : Category.Object E)
        → base (unbase x') ≡ just x'
      base-unbase x''
        with SplitFunctor.base G
          (SplitFunctor.unbase G (SplitFunctor.unbase F x''))
        | SplitFunctor.base-unbase G (SplitFunctor.unbase F x'')
      ... | _ | refl
        = SplitFunctor.base-unbase F x''
  
      map-unmap
        : {x' y' : Category.Object E}
        → (f' : Category.Arrow E x' y')
        → map (base-unbase x') (base-unbase y') (unmap f') ≡ f'
      map-unmap {x' = x''} {y' = y''} f''
        with SplitFunctor.base G
          (SplitFunctor.unbase G (SplitFunctor.unbase F x''))
        | SplitFunctor.base-unbase G (SplitFunctor.unbase F x'')
        | inspect (SplitFunctor.base G)
          (SplitFunctor.unbase G (SplitFunctor.unbase F x''))
        | SplitFunctor.base G (SplitFunctor.unbase G
          (SplitFunctor.unbase F y''))
        | SplitFunctor.base-unbase G (SplitFunctor.unbase F y'')
        | inspect (SplitFunctor.base G)
          (SplitFunctor.unbase G (SplitFunctor.unbase F y''))
      ... | _ | refl | [ p ] | _ | refl | [ q ]
        with irrelevant p
          (SplitFunctor.base-unbase G (SplitFunctor.unbase F x''))
        | irrelevant q
          (SplitFunctor.base-unbase G (SplitFunctor.unbase F y''))
      ... | refl | refl
        with SplitFunctor.map G
          (SplitFunctor.base-unbase G (SplitFunctor.unbase F x''))
          (SplitFunctor.base-unbase G (SplitFunctor.unbase F y''))
          (SplitFunctor.unmap G (SplitFunctor.unmap F f''))
        | SplitFunctor.map-unmap G (SplitFunctor.unmap F f'')
      ... | _ | refl
        = SplitFunctor.map-unmap F f''

    normalize-arrow
      : {x' : Category.Object E}
      → (x : Category.Object C)
      → base x ≡ just x'
      → Category.Arrow C x (unbase x')
    normalize-arrow x p'
      with SplitFunctor.base G x
      | inspect (SplitFunctor.base G) x
    ... | just x' | [ p ]
      = Category.compose C
        (SplitFunctor.unmap G (SplitFunctor.normalize-arrow F x' p'))
        (SplitFunctor.normalize-arrow G x p)

    abstract

      normalize-valid
        : {x' : Category.Object E}
        → (x : Category.Object C)
        → (p : base x ≡ just x')
        → map p (base-unbase x') (normalize-arrow x p) ≡ Category.identity E x'
      normalize-valid {x' = x''} x p'
        with SplitFunctor.base G x
        | inspect (SplitFunctor.base G) x
        | SplitFunctor.base G
          (SplitFunctor.unbase G (SplitFunctor.unbase F x''))
        | SplitFunctor.base-unbase G (SplitFunctor.unbase F x'')
        | inspect (SplitFunctor.base G)
          (SplitFunctor.unbase G (SplitFunctor.unbase F x''))
      ... | just x' | [ p ] | _ | refl | [ q ]
        with SplitFunctor.map G p q (Category.compose C
          (SplitFunctor.unmap G (SplitFunctor.normalize-arrow F x' p'))
          (SplitFunctor.normalize-arrow G x p))
        | SplitFunctor.map-compose G p (SplitFunctor.base-unbase G x') q
          (SplitFunctor.unmap G (SplitFunctor.normalize-arrow F x' p'))
          (SplitFunctor.normalize-arrow G x p)
        | irrelevant q
          (SplitFunctor.base-unbase G (SplitFunctor.unbase F x''))
      ... | _ | refl | refl
        with SplitFunctor.map G
          (SplitFunctor.base-unbase G x')
          (SplitFunctor.base-unbase G (SplitFunctor.unbase F x''))
          (SplitFunctor.unmap G (SplitFunctor.normalize-arrow F x' p'))
        | SplitFunctor.map-unmap G (SplitFunctor.normalize-arrow F x' p')
        | SplitFunctor.map G p (SplitFunctor.base-unbase G x')
          (SplitFunctor.normalize-arrow G x p)
        | SplitFunctor.normalize-valid G x p
      ... | _ | refl | _ | refl
        with Category.compose D
          (SplitFunctor.normalize-arrow F x' p')
          (Category.identity D x')
        | Category.precompose D (SplitFunctor.normalize-arrow F x' p')
      ... | _ | refl
        = SplitFunctor.normalize-valid F x' p'

  split-functor-compose
    : SplitFunctor D E
    → SplitFunctor C D
    → SplitFunctor C E
  split-functor-compose F G
    = record {SplitFunctorCompose F G}

-- ### Weak

module _
  {C D : Category}
  where
  
  module SplitFunctorWeak
    (F : SplitFunctor C D)
    where

    open Functor (SplitFunctor.functor F) using () renaming
      ( base
        to unbase
      ; map
        to unmap
      ; map-identity
        to unmap-identity
      ; map-compose
        to unmap-compose
      )

    map
      : (x' y' : Category.Object D)
      → Category.Arrow C (unbase x') (unbase y')
      → Category.Arrow D x' y'
    map x' y' f
      = SplitFunctor.map F
        (SplitFunctor.base-unbase F x')
        (SplitFunctor.base-unbase F y') f

    abstract

      map-compose
        : (x' y' z' : Category.Object D)
        → (f : Category.Arrow C (unbase y') (unbase z'))
        → (g : Category.Arrow C (unbase x') (unbase y'))
        → map x' z' (Category.compose C f g)
          ≡ Category.compose D (map y' z' f) (map x' y' g)
      map-compose x' y' z' f g
        = SplitFunctor.map-compose F
          (SplitFunctor.base-unbase F x')
          (SplitFunctor.base-unbase F y')
          (SplitFunctor.base-unbase F z') f g
  
      map-unmap₁
        : {y' z' : Category.Object D}
        → (x' : Category.Object D)
        → (f' : Category.Arrow D y' z')
        → (g : Category.Arrow C (unbase x') (unbase y'))
        → Category.compose D (map y' z' (unmap f')) (map x' y' g)
          ≡ Category.compose D f' (map x' y' g)
      map-unmap₁ {y' = y'} {z' = z'} x' f' g
        = sub
          (λ f → Category.compose D f (map x' y' g))
          (SplitFunctor.map-unmap F f')
  
      map-unmap₂
        : {x' y' : Category.Object D}
        → (z' : Category.Object D)
        → (f : Category.Arrow C (unbase y') (unbase z'))
        → (g' : Category.Arrow D x' y')
        → Category.compose D (map y' z' f) (map x' y' (unmap g'))
          ≡ Category.compose D (map y' z' f) g'
      map-unmap₂ {x' = x'} {y' = y'} z' f g'
        = sub
          (λ g → Category.compose D (map y' z' f) g)
          (SplitFunctor.map-unmap F g')

  split-functor-weak
    : (F : SplitFunctor C D)
    → WeakFunctor (SplitFunctor.functor F)
  split-functor-weak F
    = record {SplitFunctorWeak F}

-- ## SplitFunctorSquare

-- ### Definition

record SplitFunctorSquare
  {C₁ C₂ D₁ D₂ : Category}
  (F : Functor C₁ C₂)
  (G : Functor D₁ D₂)
  (H₁ : SplitFunctor C₁ D₁)
  (H₂ : SplitFunctor C₂ D₂)
  : Set
  where

  field

    partial-functor
      : PartialFunctorSquare F G
        (SplitFunctor.partial-functor H₁)
        (SplitFunctor.partial-functor H₂)

  open PartialFunctorSquare partial-functor public

  field

    functor
      : FunctorSquare G F
        (SplitFunctor.functor H₁)
        (SplitFunctor.functor H₂)

  open FunctorSquare functor public using () renaming
    ( base
      to unbase
    ; map
      to unmap
    )

-- ### Compose

module _
  {C₁ C₂ D₁ D₂ E₁ E₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H : Functor E₁ E₂}
  {I₁ : SplitFunctor D₁ E₁}
  {I₂ : SplitFunctor D₂ E₂}
  {J₁ : SplitFunctor C₁ D₁}
  {J₂ : SplitFunctor C₂ D₂}
  where

  module SplitFunctorSquareCompose
    (s : SplitFunctorSquare G H I₁ I₂)
    (t : SplitFunctorSquare F G J₁ J₂)
    where

    partial-functor
      : PartialFunctorSquare F H
        (SplitFunctor.partial-functor (split-functor-compose I₁ J₁))
        (SplitFunctor.partial-functor (split-functor-compose I₂ J₂))
    partial-functor
      = partial-functor-square-compose
        (SplitFunctorSquare.partial-functor s)
        (SplitFunctorSquare.partial-functor t)

    functor
      : FunctorSquare H F
        (SplitFunctor.functor (split-functor-compose I₁ J₁))
        (SplitFunctor.functor (split-functor-compose I₂ J₂))
    functor
      = functor-square-compose
        (SplitFunctorSquare.functor t)
        (SplitFunctorSquare.functor s)

  split-functor-square-compose
    : SplitFunctorSquare G H I₁ I₂
    → SplitFunctorSquare F G J₁ J₂
    → SplitFunctorSquare F H
      (split-functor-compose I₁ J₁)
      (split-functor-compose I₂ J₂)
  split-functor-square-compose s t
    = record {SplitFunctorSquareCompose s t}

-- ### Weak

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : SplitFunctor C₁ D₁}
  {H₂ : SplitFunctor C₂ D₂}
  where

  module SplitFunctorSquareWeak
    (s : SplitFunctorSquare F G H₁ H₂)
    where

    map₂
      : {x₂ y₂ : Category.Object C₂}
      → (x₂' y₂' : Category.Object D₂)
      → (p₂ : SplitFunctor.base H₂ x₂ ≡ just x₂')
      → (q₂ : SplitFunctor.base H₂ y₂ ≡ just y₂')
      → (p₂' : SplitFunctor.unbase H₂ x₂' ≡ x₂)
      → (q₂' : SplitFunctor.unbase H₂ y₂' ≡ y₂)
      → (f₂ : Category.Arrow C₂ x₂ y₂)
      → WeakFunctor.map-eq
        (split-functor-weak H₂) x₂' y₂' p₂' q₂' f₂
      ≡ SplitFunctor.map H₂ p₂ q₂ f₂
    map₂ x₂' y₂' p₂ q₂ refl refl _
      with irrelevant p₂ (SplitFunctor.base-unbase H₂ x₂')
      | irrelevant q₂ (SplitFunctor.base-unbase H₂ y₂')
    ... | refl | refl
      = refl

    map
      : (x₁' y₁' : Category.Object D₁)
      → (f₁ : Category.Arrow C₁
        (Functor.base (SplitFunctor.functor H₁) x₁')
        (Functor.base (SplitFunctor.functor H₁) y₁'))
      → WeakFunctor.map-eq
        (split-functor-weak H₂)
        (Functor.base G x₁')
        (Functor.base G y₁')
        (FunctorSquare.base (SplitFunctorSquare.functor s) x₁')
        (FunctorSquare.base (SplitFunctorSquare.functor s) y₁')
        (Functor.map F f₁)
      ≡ Functor.map G
        (WeakFunctor.map (split-functor-weak H₁) x₁' y₁' f₁)
    map x₁' y₁' f₁
      = trans
        (map₂
          (Functor.base G x₁')
          (Functor.base G y₁')
          (SplitFunctorSquare.base s
            (SplitFunctor.unbase H₁ x₁')
            (SplitFunctor.base-unbase H₁ x₁'))
          (SplitFunctorSquare.base s
            (SplitFunctor.unbase H₁ y₁')
            (SplitFunctor.base-unbase H₁ y₁'))
          (SplitFunctorSquare.unbase s x₁')
          (SplitFunctorSquare.unbase s y₁')
          (Functor.map F f₁))
        (SplitFunctorSquare.map s
          (SplitFunctor.base-unbase H₁ x₁')
          (SplitFunctor.base-unbase H₁ y₁') f₁)

  split-functor-square-weak
    : (s : SplitFunctorSquare F G H₁ H₂)
    → WeakFunctorSquare
      (split-functor-weak H₁)
      (split-functor-weak H₂)
      (SplitFunctorSquare.functor s)
  split-functor-square-weak s
    = record {SplitFunctorSquareWeak s}

-- ## SplitFunctorSquare'

module _SplitFunctorSquare' where

  data SplitFunctorSquare'
    : {C₁ C₂ D₁ D₂ D₃ : Category}
    → Functor C₁ C₂
    → Functor D₁ D₃
    → SplitFunctor C₁ D₁
    → SplitFunctor C₂ D₂
    → Set
    where
  
    split-functor-square'
      : {C₁ C₂ D₁ D₂ : Category}
      → {F : Functor C₁ C₂}
      → {G : Functor D₁ D₂}
      → {H₁ : SplitFunctor C₁ D₁}
      → {H₂ : SplitFunctor C₂ D₂}
      → SplitFunctorSquare F G H₁ H₂
      → SplitFunctorSquare' F G H₁ H₂

SplitFunctorSquare'
  : {C₁ C₂ D₁ D₂ D₃ : Category}
  → Functor C₁ C₂
  → Functor D₁ D₃
  → SplitFunctor C₁ D₁
  → SplitFunctor C₂ D₂
  → Set
SplitFunctorSquare'
  = _SplitFunctorSquare'.SplitFunctorSquare'

open _SplitFunctorSquare'.SplitFunctorSquare' public

module SplitFunctorSquare' where

  partial-functor
    : {C₁ C₂ D₁ D₂ D₃ : Category}
    → {F : Functor C₁ C₂}
    → {G : Functor D₁ D₃}
    → {H₁ : SplitFunctor C₁ D₁}
    → {H₂ : SplitFunctor C₂ D₂}
    → SplitFunctorSquare' F G H₁ H₂
    → PartialFunctorSquare' F G
      (SplitFunctor.partial-functor H₁)
      (SplitFunctor.partial-functor H₂)
  partial-functor (split-functor-square' s)
    = partial-functor-square' (SplitFunctorSquare.partial-functor s)
  
  functor
    : {A : Set}
    → {x₁ x₂ : A}
    → {C₁ D₁ : Category}
    → (C₂ D₂ : A → Category)
    → {F : Functor C₁ (C₂ x₁)}
    → {G : Functor D₁ (D₂ x₂)}
    → {H₁ : SplitFunctor C₁ D₁}
    → (H₂ : (x : A) → SplitFunctor (C₂ x) (D₂ x))
    → x₁ ≡ x₂
    → SplitFunctorSquare' F G H₁ (H₂ x₁)
    → FunctorSquare G F
      (SplitFunctor.functor H₁)
      (SplitFunctor.functor (H₂ x₂))
  functor _ _ _ refl (split-functor-square' s)
    = SplitFunctorSquare.functor s

-- ## SplitDependentFunctor

record SplitDependentFunctor
  {C : Category}
  (C' D' : DependentCategory C)
  : Set
  where

  no-eta-equality

  field

    split-functor
      : (x : Category.Object C)
      → SplitFunctor
        (DependentCategory.category C' x)
        (DependentCategory.category D' x)

    split-functor-square
      : {x y : Category.Object C}
      → (f : Category.Arrow C x y)
      → SplitFunctorSquare
        (DependentCategory.functor C' f)
        (DependentCategory.functor D' f)
        (split-functor x)
        (split-functor y)

  partial-dependent-functor
    : PartialDependentFunctor C' D'
  partial-dependent-functor
    = record
    { partial-functor
      = SplitFunctor.partial-functor ∘ split-functor
    ; partial-functor-square
      = SplitFunctorSquare.partial-functor ∘ split-functor-square
    }

  open PartialDependentFunctor partial-dependent-functor public

  dependent-functor
    : DependentFunctor D' C'
  dependent-functor
    = record
    { functor
      = functor-identity' C
    ; functor'
      = SplitFunctor.functor ∘ split-functor
    ; functor-square
      = SplitFunctorSquare.functor ∘ split-functor-square
    }

  open DependentFunctor dependent-functor public using () renaming
    ( functor'
      to functor
    ; base'
      to unbase
    ; map'
      to unmap
    ; map-identity'
      to unmap-identity
    ; map-compose'
      to unmap-compose
    ; map-compose-eq'
      to unmap-compose-eq
    ; functor-square
      to functor-square
    ; base-commutative
      to unbase-commutative
    ; map-commutative
      to unmap-commutative
    )

  base-unbase
    : (x : Category.Object C)
    → (x' : DependentCategory.Object D' x)
    → base x (unbase x x') ≡ just x'
  base-unbase x
    = SplitFunctor.base-unbase
      (split-functor x)

  map-unmap
    : (x : Category.Object C)
    → {x' y' : DependentCategory.Object D' x}
    → (f : DependentCategory.Arrow D' x x' y')
    → map x (base-unbase x x') (base-unbase x y') (unmap x f) ≡ f
  map-unmap x
    = SplitFunctor.map-unmap
      (split-functor x)

  normalize-arrow
    : (x : Category.Object C)
    → {x'' : DependentCategory.Object D' x}
    → (x' : DependentCategory.Object C' x)
    → base x x' ≡ just x''
    → DependentCategory.Arrow C' x x' (unbase x x'')
  normalize-arrow x
    = SplitFunctor.normalize-arrow
      (split-functor x)

  normalize-valid
    : (x : Category.Object C)
    → {x'' : DependentCategory.Object D' x}
    → (x' : DependentCategory.Object C' x)
    → (p : base x x' ≡ just x'')
    → map x p (base-unbase x x'') (normalize-arrow x x' p)
      ≡ DependentCategory.identity D' x x''
  normalize-valid x
    = SplitFunctor.normalize-valid
      (split-functor x)

-- ## SplitDependentFunctorSquare

record SplitDependentFunctorSquare
  {C₁ C₂ : Category}
  {C₁' D₁' : DependentCategory C₁}
  {C₂' D₂' : DependentCategory C₂}
  (F : DependentFunctor C₁' C₂')
  (G : DependentFunctor D₁' D₂')
  (H₁ : SplitDependentFunctor C₁' D₁')
  (H₂ : SplitDependentFunctor C₂' D₂')
  : Set
  where

  field

    functor
      : FunctorEqual
        (DependentFunctor.functor F)
        (DependentFunctor.functor G)

  open FunctorEqual functor public

  field

    split-functor
      : (x₁ : Category.Object C₁)
      → SplitFunctorSquare'
        (DependentFunctor.functor' F x₁)
        (DependentFunctor.functor' G x₁)
        (SplitDependentFunctor.split-functor H₁ x₁)
        (SplitDependentFunctor.split-functor H₂ (DependentFunctor.base F x₁))

  partial-dependent-functor
    : PartialDependentFunctorSquare F G
      (SplitDependentFunctor.partial-dependent-functor H₁)
      (SplitDependentFunctor.partial-dependent-functor H₂)
  partial-dependent-functor
    = record
    { functor
      = functor
    ; partial-functor
      = λ x₁ → SplitFunctorSquare'.partial-functor
        (split-functor x₁)
    }

  dependent-functor
    : DependentFunctorSquare G F
      (SplitDependentFunctor.dependent-functor H₁)
      (SplitDependentFunctor.dependent-functor H₂)
  dependent-functor
    = record
    { functor
      = functor-square-identity-eq (functor-sym functor)
    ; functor'
      = λ x₁ → SplitFunctorSquare'.functor
        (DependentCategory.category C₂')
        (DependentCategory.category D₂')
        (SplitDependentFunctor.split-functor H₂)
        (FunctorEqual.base functor x₁)
        (split-functor x₁)
    }

