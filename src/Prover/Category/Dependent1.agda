module Prover.Category.Dependent1 where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare; functor-compose'; functor-compose-to-equal;
    functor-identity'; functor-identity-to-equal; functor-square-compose;
    functor-square-identity; functor-square-to-equal)
open import Prover.Category.Chain
  using (chain₁-category; chain₁-functor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare)

-- ## Dependent₁Category

Dependent₁Category
  : Category
  → Set₁
Dependent₁Category C
  = DependentCategory
    (chain₁-category C)

module Dependent₁Category
  {C : Category}
  (C' : Dependent₁Category C)
  where

  open DependentCategory C' public

  open module Category' x
    = Category (category x)
    public

  open module Functor' {x = x} {y = y} f
    = Functor (functor {x = x} {y = y} f)
    public using () renaming
    ( base
      to base
    ; map
      to map
    ; map-identity
      to map-identity'
    ; map-compose-eq
      to map-compose-eq
    )

  open module FunctorIdentity' x
    = FunctorIdentity (functor-identity x)
    public using () renaming
    ( base
      to base-identity
    ; map
      to map-identity
    )

  open module FunctorCompose' {x = x} {y = y} {z = z} f g
    = FunctorCompose (functor-compose {x = x} {y = y} {z = z} f g)
    public using () renaming
    ( base
      to base-compose
    ; map
      to map-compose
    )

-- ## Dependent₁Functor

-- ### Definition

Dependent₁Functor
  : {C D : Category}
  → Dependent₁Category C
  → Dependent₁Category D
  → Functor C D
  → Set
Dependent₁Functor C' D' F
  = DependentFunctor C' D'
    (chain₁-functor F)

module Dependent₁Functor
  {C D : Category}
  {C' : Dependent₁Category C}
  {D' : Dependent₁Category D}
  {F : Functor C D}
  (F' : Dependent₁Functor C' D' F)
  where

  open DependentFunctor F' public

  open module Functor' x
    = Functor (functor x)
    public

  open module FunctorSquare' {x = x} {y = y} f
    = FunctorSquare (functor-square {x = x} {y = y} f)
    public using () renaming
    ( base
      to base-square
    ; map
      to map-square
    )

-- ### Identity

dependent₁-functor-identity
  : {C : Category}
  → (C' : Dependent₁Category C)
  → Dependent₁Functor C' C' (functor-identity' C)
dependent₁-functor-identity C'
  = record
  { functor
    = λ x → functor-identity'
      (Dependent₁Category.category C' x)
  ; functor-square
    = λ f → functor-square-identity
      (Dependent₁Category.functor C' f)
  }

-- ### Compose

dependent₁-functor-compose
  : {C D E : Category}
  → {C' : Dependent₁Category C}
  → {D' : Dependent₁Category D}
  → {E' : Dependent₁Category E}
  → {F : Functor D E}
  → {G : Functor C D}
  → Dependent₁Functor D' E' F
  → Dependent₁Functor C' D' G
  → Dependent₁Functor C' E' (functor-compose' F G)
dependent₁-functor-compose {G = G} F' G'
  = record
  { functor
    = λ x → functor-compose'
      (Dependent₁Functor.functor F' (Functor.base G x))
      (Dependent₁Functor.functor G' x)
  ; functor-square
    = λ f → functor-square-compose
      (Dependent₁Functor.functor-square F' (Functor.map G f))
      (Dependent₁Functor.functor-square G' f)
  }

-- ## Dependent₁FunctorEqual

record Dependent₁FunctorEqual
  {C D : Category}
  {C' : Dependent₁Category C}
  {D' : Dependent₁Category D}
  {F₁ F₂ : Functor C D}
  (F₁' : Dependent₁Functor C' D' F₁)
  (F₂' : Dependent₁Functor C' D' F₂)
  : Set
  where

  field

    functor
      : FunctorEqual F₁ F₂

  open FunctorEqual functor public

  field

    functor'
      : (x : Category.Object C)
      → FunctorEqual
        (Dependent₁Functor.functor F₁' x)
        (Dependent₁Functor.functor F₂' x)

  open module Functor' x
    = FunctorEqual (functor' x)
    public using () renaming
    ( base
      to base'
    ; map
      to map'
    )

-- ## Dependent₁FunctorIdentity

-- ### Definition

Dependent₁FunctorIdentity
  : {C : Category}
  → {C' : Dependent₁Category C}
  → {F : Functor C C}
  → Dependent₁Functor C' C' F
  → Set
Dependent₁FunctorIdentity
  = DependentFunctorIdentity

module Dependent₁FunctorIdentity
  {C : Category}
  {C' : Dependent₁Category C}
  {F : Functor C C}
  {F' : Dependent₁Functor C' C' F}
  (p : Dependent₁FunctorIdentity F')
  where

  open DependentFunctorIdentity p public

-- ### Equality

dependent₁-functor-identity-to-equal
  : {C : Category}
  → {C' : Dependent₁Category C}
  → {F : Functor C C}
  → {F' : Dependent₁Functor C' C' F}
  → FunctorIdentity F
  → Dependent₁FunctorIdentity F'
  → Dependent₁FunctorEqual F'
    (dependent₁-functor-identity C')
dependent₁-functor-identity-to-equal p p'
  = record
  { functor
    = functor-identity-to-equal p
  ; functor'
    = λ x → functor-identity-to-equal
      (Dependent₁FunctorIdentity.functor p' x)
  }

-- ## Dependent₁FunctorCompose

-- ### Definition

Dependent₁FunctorCompose
  : {C D E : Category}
  → {C' : Dependent₁Category C}
  → {D' : Dependent₁Category D}
  → {E' : Dependent₁Category E}
  → {F : Functor D E}
  → {G : Functor C D}
  → {H : Functor C E}
  → Dependent₁Functor D' E' F
  → Dependent₁Functor C' D' G
  → Dependent₁Functor C' E' H
  → Set
Dependent₁FunctorCompose
  = DependentFunctorCompose

module Dependent₁FunctorCompose
  {C D E : Category}
  {C' : Dependent₁Category C}
  {D' : Dependent₁Category D}
  {E' : Dependent₁Category E}
  {F : Functor D E}
  {G : Functor C D}
  {H : Functor C E}
  {F' : Dependent₁Functor D' E' F}
  {G' : Dependent₁Functor C' D' G}
  {H' : Dependent₁Functor C' E' H}
  (p : Dependent₁FunctorCompose F' G' H')
  where

  open DependentFunctorCompose p public

-- ### Equality

dependent₁-functor-compose-to-equal
  : {C D E : Category}
  → {C' : Dependent₁Category C}
  → {D' : Dependent₁Category D}
  → {E' : Dependent₁Category E}
  → {F : Functor D E}
  → {G : Functor C D}
  → {H : Functor C E}
  → {F' : Dependent₁Functor D' E' F}
  → {G' : Dependent₁Functor C' D' G}
  → {H' : Dependent₁Functor C' E' H}
  → FunctorCompose F G H
  → Dependent₁FunctorCompose F' G' H'
  → Dependent₁FunctorEqual H'
    (dependent₁-functor-compose F' G')
dependent₁-functor-compose-to-equal p p'
  = record
  { functor
    = functor-compose-to-equal p
  ; functor'
    = λ x → functor-compose-to-equal
      (Dependent₁FunctorCompose.functor p' x)
  }

-- ## Dependent₁FunctorSquare

-- ### Definition

Dependent₁FunctorSquare
  : {C₁ C₂ D₁ D₂ : Category}
  → {C₁' : Dependent₁Category C₁}
  → {C₂' : Dependent₁Category C₂}
  → {D₁' : Dependent₁Category D₁}
  → {D₂' : Dependent₁Category D₂}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → Dependent₁Functor C₁' C₂' F
  → Dependent₁Functor D₁' D₂' G
  → Dependent₁Functor C₁' D₁' H₁
  → Dependent₁Functor C₂' D₂' H₂
  → Set
Dependent₁FunctorSquare
  = DependentFunctorSquare

module Dependent₁FunctorSquare
  {C₁ C₂ D₁ D₂ : Category}
  {C₁' : Dependent₁Category C₁}
  {C₂' : Dependent₁Category C₂}
  {D₁' : Dependent₁Category D₁}
  {D₂' : Dependent₁Category D₂}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : Functor C₁ D₁}
  {H₂ : Functor C₂ D₂}
  {F' : Dependent₁Functor C₁' C₂' F}
  {G' : Dependent₁Functor D₁' D₂' G}
  {H₁' : Dependent₁Functor C₁' D₁' H₁}
  {H₂' : Dependent₁Functor C₂' D₂' H₂}
  (s : Dependent₁FunctorSquare F' G' H₁' H₂')
  where

  open DependentFunctorSquare s public

-- ### Equality

dependent₁-functor-square-to-equal
  : {C₁ C₂ D₁ D₂ : Category}
  → {C₁' : Dependent₁Category C₁}
  → {C₂' : Dependent₁Category C₂}
  → {D₁' : Dependent₁Category D₁}
  → {D₂' : Dependent₁Category D₂}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → {F' : Dependent₁Functor C₁' C₂' F}
  → {G' : Dependent₁Functor D₁' D₂' G}
  → {H₁' : Dependent₁Functor C₁' D₁' H₁}
  → {H₂' : Dependent₁Functor C₂' D₂' H₂}
  → FunctorSquare F G H₁ H₂
  → Dependent₁FunctorSquare F' G' H₁' H₂'
  → Dependent₁FunctorEqual
    (dependent₁-functor-compose H₂' F')
    (dependent₁-functor-compose G' H₁')
dependent₁-functor-square-to-equal s s'
  = record
  { functor
    = functor-square-to-equal s
  ; functor'
    = λ x → functor-square-to-equal
      (Dependent₁FunctorSquare.functor s' x)
  }

