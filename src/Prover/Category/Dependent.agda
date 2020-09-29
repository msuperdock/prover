module Prover.Category.Dependent where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

DependentCategory
  : {n : ℕ}
  → ChainCategory n
  → Set₁

record DependentCategory'
  {n : ℕ}
  (C : ChainCategory (suc n))
  : Set₁

-- ### DependentFunctor

DependentFunctor
  : {n : ℕ}
  → {C D : ChainCategory n}
  → DependentCategory C
  → DependentCategory D
  → ChainFunctor C D
  → Set

record DependentFunctor'
  {n : ℕ}
  {C D : ChainCategory (suc n)}
  (C' : DependentCategory C)
  (D' : DependentCategory D)
  (F : ChainFunctor C D)
  : Set

-- ### DependentFunctorIdentity

DependentFunctorIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → DependentFunctor C₁' C₂' F
  → Set
  
record DependentFunctorIdentity'
  {n : ℕ}
  {C₁ C₂ : ChainCategory (suc n)}
  {C₁' : DependentCategory C₁}
  {C₂' : DependentCategory C₂}
  {F : ChainFunctor C₁ C₂}
  (F' : DependentFunctor C₁' C₂' F)
  : Set
  
-- ### DependentFunctorCompose

DependentFunctorCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {E₁' : DependentCategory E₁}
  → {E₂' : DependentCategory E₂}
  → {F : ChainFunctor D E₁}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E₂}
  → DependentFunctor D' E₁' F
  → DependentFunctor C' D' G
  → DependentFunctor C' E₂' H
  → Set
  
record DependentFunctorCompose'
  {n : ℕ}
  {C D E₁ E₂ : ChainCategory (suc n)}
  {C' : DependentCategory C}
  {D' : DependentCategory D}
  {E₁' : DependentCategory E₁}
  {E₂' : DependentCategory E₂}
  {F : ChainFunctor D E₁}
  {G : ChainFunctor C D}
  {H : ChainFunctor C E₂}
  (F' : DependentFunctor D' E₁' F)
  (G' : DependentFunctor C' D' G)
  (H' : DependentFunctor C' E₂' H)
  : Set

-- ### DependentFunctorSquare

DependentFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {D₁' : DependentCategory D₁}
  → {D₂' : DependentCategory D₂}
  → {D₃' : DependentCategory D₃}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₃}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → DependentFunctor C₁' C₂' F
  → DependentFunctor D₁' D₃' G
  → DependentFunctor C₁' D₁' H₁
  → DependentFunctor C₂' D₂' H₂
  → Set

record DependentFunctorSquare'
  {n : ℕ}
  {C₁ C₂ D₁ D₂ D₃ : ChainCategory (suc n)}
  {C₁' : DependentCategory C₁}
  {C₂' : DependentCategory C₂}
  {D₁' : DependentCategory D₁}
  {D₂' : DependentCategory D₂}
  {D₃' : DependentCategory D₃}
  {F : ChainFunctor C₁ C₂}
  {G : ChainFunctor D₁ D₃}
  {H₁ : ChainFunctor C₁ D₁}
  {H₂ : ChainFunctor C₂ D₂}
  (F' : DependentFunctor C₁' C₂' F)
  (G' : DependentFunctor D₁' D₃' G)
  (H₁' : DependentFunctor C₁' D₁' H₁)
  (H₂' : DependentFunctor C₂' D₂' H₂)
  : Set

-- ## Definitions

-- ### DependentCategory

DependentCategory {n = zero} _
  = Category
DependentCategory {n = suc _} C
  = DependentCategory' C

record DependentCategory' C where

  inductive

  no-eta-equality

  field

    category
      : (x : ChainCategory.Object C)
      → DependentCategory
        (ChainCategory.category' C x)

    functor
      : {x y : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C x y)
      → DependentFunctor
        (category x)
        (category y)
        (ChainCategory.functor C f)

    functor-identity
      : (x : ChainCategory.Object C)
      → DependentFunctorIdentity
        (functor (ChainCategory.identity C x))

    functor-compose
      : {x y z : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C y z)
      → (g : ChainCategory.Arrow C x y)
      → DependentFunctorCompose
        (functor f)
        (functor g)
        (functor (ChainCategory.compose C f g))

module DependentCategory
  = DependentCategory'

-- ### DependentFunctor

DependentFunctor {n = zero} C' D' _
  = Functor C' D'
DependentFunctor {n = suc _} C' D' F
  = DependentFunctor' C' D' F

record DependentFunctor' {_ C} C' D' F where

  inductive

  no-eta-equality

  field

    functor
      : (x : ChainCategory.Object C)
      → DependentFunctor
        (DependentCategory.category C' x)
        (DependentCategory.category D' (ChainFunctor.base F x))
        (ChainFunctor.functor' F x)

    functor-square
      : {x y : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C x y)
      → DependentFunctorSquare
        (DependentCategory.functor C' f)
        (DependentCategory.functor D' (ChainFunctor.map F f))
        (functor x)
        (functor y)

module DependentFunctor
  = DependentFunctor'

-- ### DependentFunctorIdentity

DependentFunctorIdentity {n = zero}
  = FunctorIdentity
DependentFunctorIdentity {n = suc _}
  = DependentFunctorIdentity'

record DependentFunctorIdentity' {_ C₁} F' where

  inductive

  field

    functor
      : (x₁ : ChainCategory.Object C₁)
      → DependentFunctorIdentity
        (DependentFunctor.functor F' x₁)

module DependentFunctorIdentity
  = DependentFunctorIdentity'

-- ### DependentFunctorCompose

DependentFunctorCompose {n = zero}
  = FunctorCompose
DependentFunctorCompose {n = suc _}
  = DependentFunctorCompose'

record DependentFunctorCompose' {_ C _ _ _ _ _ _ _ _ G} F' G' H' where

  inductive

  field

    functor
      : (x : ChainCategory.Object C)
      → DependentFunctorCompose
        (DependentFunctor.functor F' (ChainFunctor.base G x))
        (DependentFunctor.functor G' x)
        (DependentFunctor.functor H' x)

module DependentFunctorCompose
  = DependentFunctorCompose'

-- ### DependentFunctorSquare

DependentFunctorSquare {n = zero}
  = FunctorSquare
DependentFunctorSquare {n = suc _}
  = DependentFunctorSquare'

record DependentFunctorSquare'
  {_ C₁ _ _ _ _ _ _ _ _ _ F _ H₁} F' G' H₁' H₂'
  where

  inductive

  field

    functor
      : (x₁ : ChainCategory.Object C₁)
      → DependentFunctorSquare
        (DependentFunctor.functor F' x₁)
        (DependentFunctor.functor G' (ChainFunctor.base H₁ x₁))
        (DependentFunctor.functor H₁' x₁)
        (DependentFunctor.functor H₂' (ChainFunctor.base F x₁))

module DependentFunctorSquare
  = DependentFunctorSquare'

