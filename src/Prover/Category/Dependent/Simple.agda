module Prover.Category.Dependent.Simple where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Function
  using (Function; FunctionCompose; FunctionIdentity; FunctionSquare)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Prelude

-- ## Types

-- ### DependentSimpleCategory

DependentSimpleCategory
  : {n : ℕ}
  → ChainCategory n
  → Set₁

record DependentSimpleCategory'
  {n : ℕ}
  (C : ChainCategory (suc n))
  : Set₁

-- ### DependentSimpleFunctor

DependentSimpleFunctor
  : {n : ℕ}
  → {C D : ChainCategory n}
  → DependentSimpleCategory C
  → DependentSimpleCategory D
  → ChainFunctor C D
  → Set

record DependentSimpleFunctor'
  {n : ℕ}
  {C D : ChainCategory (suc n)}
  (C' : DependentSimpleCategory C)
  (D' : DependentSimpleCategory D)
  (F : ChainFunctor C D)
  : Set

-- ### DependentSimpleFunctorIdentity

DependentSimpleFunctorIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → DependentSimpleFunctor C₁' C₂' F
  → Set

record DependentSimpleFunctorIdentity'
  {n : ℕ}
  {C₁ C₂ : ChainCategory (suc n)}
  {C₁' : DependentSimpleCategory C₁}
  {C₂' : DependentSimpleCategory C₂}
  {F : ChainFunctor C₁ C₂}
  (F' : DependentSimpleFunctor C₁' C₂' F)
  : Set

-- ### DependentSimpleFunctorCompose

DependentSimpleFunctorCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {E₁' : DependentSimpleCategory E₁}
  → {E₂' : DependentSimpleCategory E₂}
  → {F : ChainFunctor D E₁}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E₂}
  → DependentSimpleFunctor D' E₁' F
  → DependentSimpleFunctor C' D' G
  → DependentSimpleFunctor C' E₂' H
  → Set

record DependentSimpleFunctorCompose'
  {n : ℕ}
  {C D E₁ E₂ : ChainCategory (suc n)}
  {C' : DependentSimpleCategory C}
  {D' : DependentSimpleCategory D}
  {E₁' : DependentSimpleCategory E₁}
  {E₂' : DependentSimpleCategory E₂}
  {F : ChainFunctor D E₁}
  {G : ChainFunctor C D}
  {H : ChainFunctor C E₂}
  (F' : DependentSimpleFunctor D' E₁' F)
  (G' : DependentSimpleFunctor C' D' G)
  (H' : DependentSimpleFunctor C' E₂' H)
  : Set

-- ### DependentSimpleFunctorSquare

DependentSimpleFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {D₁' : DependentSimpleCategory D₁}
  → {D₂' : DependentSimpleCategory D₂}
  → {D₃' : DependentSimpleCategory D₃}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₃}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → DependentSimpleFunctor C₁' C₂' F
  → DependentSimpleFunctor D₁' D₃' G
  → DependentSimpleFunctor C₁' D₁' H₁
  → DependentSimpleFunctor C₂' D₂' H₂
  → Set
  
record DependentSimpleFunctorSquare'
  {n : ℕ}
  {C₁ C₂ D₁ D₂ D₃ : ChainCategory (suc n)}
  {C₁' : DependentSimpleCategory C₁}
  {C₂' : DependentSimpleCategory C₂}
  {D₁' : DependentSimpleCategory D₁}
  {D₂' : DependentSimpleCategory D₂}
  {D₃' : DependentSimpleCategory D₃}
  {F : ChainFunctor C₁ C₂}
  {G : ChainFunctor D₁ D₃}
  {H₁ : ChainFunctor C₁ D₁}
  {H₂ : ChainFunctor C₂ D₂}
  (F' : DependentSimpleFunctor C₁' C₂' F)
  (G' : DependentSimpleFunctor D₁' D₃' G)
  (H₁' : DependentSimpleFunctor C₁' D₁' H₁)
  (H₂' : DependentSimpleFunctor C₂' D₂' H₂)
  : Set
  
-- ## Definitions

-- ### DependentSimpleCategory

DependentSimpleCategory {n = zero} _
  = Set
DependentSimpleCategory {n = suc _} C
  = DependentSimpleCategory' C

record DependentSimpleCategory' C where

  inductive

  no-eta-equality

  field

    category
      : (x : ChainCategory.Object C)
      → DependentSimpleCategory
        (ChainCategory.category' C x)

    functor
      : {x y : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C x y)
      → DependentSimpleFunctor
        (category x)
        (category y)
        (ChainCategory.functor C f)

    functor-identity
      : (x : ChainCategory.Object C)
      → DependentSimpleFunctorIdentity
        (functor (ChainCategory.identity C x))

    functor-compose
      : {x y z : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C y z)
      → (g : ChainCategory.Arrow C x y)
      → DependentSimpleFunctorCompose
        (functor f)
        (functor g)
        (functor (ChainCategory.compose C f g))

module DependentSimpleCategory
  = DependentSimpleCategory'

-- ### DependentSimpleFunctor

DependentSimpleFunctor {n = zero} C' D' _
  = Function C' D'
DependentSimpleFunctor {n = suc _} C' D' F
  = DependentSimpleFunctor' C' D' F

record DependentSimpleFunctor' {_ C} C' D' F where

  inductive

  no-eta-equality

  field

    functor
      : (x : ChainCategory.Object C)
      → DependentSimpleFunctor
        (DependentSimpleCategory.category C' x)
        (DependentSimpleCategory.category D' (ChainFunctor.base F x))
        (ChainFunctor.functor' F x)

    functor-square
      : {x y : ChainCategory.Object C}
      → (f : ChainCategory.Arrow C x y)
      → DependentSimpleFunctorSquare
        (DependentSimpleCategory.functor C' f)
        (DependentSimpleCategory.functor D' (ChainFunctor.map F f))
        (functor x)
        (functor y)

module DependentSimpleFunctor
  = DependentSimpleFunctor'

-- ### DependentSimpleFunctorIdentity

DependentSimpleFunctorIdentity {n = zero}
  = FunctionIdentity
DependentSimpleFunctorIdentity {n = suc _}
  = DependentSimpleFunctorIdentity'

record DependentSimpleFunctorIdentity' {_ C₁} F' where

  inductive

  field

    functor
      : (x₁ : ChainCategory.Object C₁)
      → DependentSimpleFunctorIdentity
        (DependentSimpleFunctor.functor F' x₁)

module DependentSimpleFunctorIdentity
  = DependentSimpleFunctorIdentity'

-- ### DependentSimpleFunctorCompose

DependentSimpleFunctorCompose {n = zero}
  = FunctionCompose
DependentSimpleFunctorCompose {n = suc _}
  = DependentSimpleFunctorCompose'

record DependentSimpleFunctorCompose' {_ C _ _ _ _ _ _ _ _ G} F' G' H' where

  inductive

  field
    
    functor
      : (x : ChainCategory.Object C)
      → DependentSimpleFunctorCompose
        (DependentSimpleFunctor.functor F' (ChainFunctor.base G x))
        (DependentSimpleFunctor.functor G' x)
        (DependentSimpleFunctor.functor H' x)

module DependentSimpleFunctorCompose
  = DependentSimpleFunctorCompose'

-- ### DependentSimpleFunctorSquare

DependentSimpleFunctorSquare {n = zero}
  = FunctionSquare
DependentSimpleFunctorSquare {n = suc _}
  = DependentSimpleFunctorSquare'

record DependentSimpleFunctorSquare'
  {_ C₁ _ _ _ _ _ _ _ _ _ F _ H₁} F' G' H₁' H₂'
  where

  inductive

  field

    functor
      : (x₁ : ChainCategory.Object C₁)
      → DependentSimpleFunctorSquare
        (DependentSimpleFunctor.functor F' x₁)
        (DependentSimpleFunctor.functor G' (ChainFunctor.base H₁ x₁))
        (DependentSimpleFunctor.functor H₁' x₁)
        (DependentSimpleFunctor.functor H₂' (ChainFunctor.base F x₁))

module DependentSimpleFunctorSquare
  = DependentSimpleFunctorSquare'

-- ## Conversion

dependent-simple-category-set
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentSet C

dependent-simple-category-set {n = zero} C'
  = C'

dependent-simple-category-set {n = suc _} C'
  = record
  { set
    = λ x → dependent-simple-category-set
      (DependentSimpleCategory.category C' x)
  }

