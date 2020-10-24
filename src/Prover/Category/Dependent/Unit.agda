module Prover.Category.Dependent.Unit where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorEqual;
    ChainFunctorIdentity; ChainFunctorSquare)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorEqual; DependentFunctorIdentity; DependentFunctorSquare)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; DependentSimpleFunctor;
    DependentSimpleFunctorCompose; DependentSimpleFunctorEqual;
    DependentSimpleFunctorIdentity; DependentSimpleFunctorSquare)
open import Prover.Category.Unit
  using (category-unit; functor-compose-unit; functor-equal-unit;
    functor-identity-unit; functor-square-unit; functor-unit)
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

dependent-category-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentCategory C

-- ### DependentFunctor

dependent-functor-unit
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {F : ChainFunctor C D}
  → DependentSimpleFunctor C' D' F
  → DependentFunctor
    (dependent-category-unit C')
    (dependent-category-unit D') F

-- ### DependentFunctorEqual

dependent-functor-equal-unit
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {F₁ F₂ : ChainFunctor C D}
  → {F₁' : DependentSimpleFunctor C' D' F₁}
  → {F₂' : DependentSimpleFunctor C' D' F₂}
  → ChainFunctorEqual F₁ F₂
  → DependentSimpleFunctorEqual F₁' F₂'
  → DependentFunctorEqual
    (dependent-functor-unit F₁')
    (dependent-functor-unit F₂')

dependent-functor-equal-unit'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C : ChainCategory n}
  → (D : A → ChainCategory n)
  → {C' : DependentSimpleCategory C}
  → (D' : (x : A) → DependentSimpleCategory (D x))
  → {F₁ : ChainFunctor C (D x₁)}
  → {F₂ : ChainFunctor C (D x₂)}
  → {F₁' : DependentSimpleFunctor C' (D' x₁) F₁}
  → {F₂' : DependentSimpleFunctor C' (D' x₂) F₂}
  → x₁ ≡ x₂
  → ChainFunctorEqual F₁ F₂
  → DependentSimpleFunctorEqual F₁' F₂'
  → DependentFunctorEqual
    (dependent-functor-unit F₁')
    (dependent-functor-unit F₂')

-- ### DependentFunctorIdentity

dependent-functor-identity-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {F : ChainFunctor C C}
  → {F' : DependentSimpleFunctor C' C' F}
  → ChainFunctorIdentity F
  → DependentSimpleFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-unit F')

dependent-functor-identity-unit'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → DependentSimpleCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : DependentSimpleFunctor (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → ChainFunctorIdentity F
  → DependentSimpleFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-unit F')

-- ### DependentFunctorCompose

dependent-functor-compose-unit
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {E' : DependentSimpleCategory E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : DependentSimpleFunctor D' E' F}
  → {G' : DependentSimpleFunctor C' D' G}
  → {H' : DependentSimpleFunctor C' E' H}
  → ChainFunctorCompose F G H
  → DependentSimpleFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-unit F')
    (dependent-functor-unit G')
    (dependent-functor-unit H')

dependent-functor-compose-unit'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → (E' : (x : A) → DependentSimpleCategory (E x))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F' : DependentSimpleFunctor D' (E' x₁) F}
  → {G' : DependentSimpleFunctor C' D' G}
  → {H' : DependentSimpleFunctor C' (E' x₂) H}
  → x₂ ≡ x₁
  → ChainFunctorCompose F G H
  → DependentSimpleFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-unit F')
    (dependent-functor-unit G')
    (dependent-functor-unit H')

-- ### DependentFunctorSquare

dependent-functor-square-unit
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {D₁' : DependentSimpleCategory D₁}
  → {D₂' : DependentSimpleCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : DependentSimpleFunctor C₁' C₂' F}
  → {G' : DependentSimpleFunctor D₁' D₂' G}
  → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
  → {H₂' : DependentSimpleFunctor C₂' D₂' H₂}
  → ChainFunctorSquare F G H₁ H₂
  → DependentSimpleFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-unit F')
    (dependent-functor-unit G')
    (dependent-functor-unit H₁')
    (dependent-functor-unit H₂')

dependent-functor-square-unit'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {D₁' : DependentSimpleCategory D₁}
  → (D₂' : (x : A) → DependentSimpleCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F' : DependentSimpleFunctor C₁' C₂' F}
  → {G' : DependentSimpleFunctor D₁' (D₂' x₁) G}
  → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
  → {H₂' : DependentSimpleFunctor C₂' (D₂' x₂) H₂}
  → x₂ ≡ x₁
  → ChainFunctorSquare F G H₁ H₂
  → DependentSimpleFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-unit F')
    (dependent-functor-unit G')
    (dependent-functor-unit H₁')
    (dependent-functor-unit H₂')

-- ## Definitions

-- ### DependentCategory

dependent-category-unit {n = zero} C'
  = category-unit C'

dependent-category-unit {n = suc _} {C = C} C'
  = record
  { category
    = λ x → dependent-category-unit
      (DependentSimpleCategory.category C' x)
  ; functor
    = λ f → dependent-functor-unit
      (DependentSimpleCategory.functor C' f)
  ; functor-equal
    = λ p → dependent-functor-equal-unit
      (ChainCategory.functor-equal C p)
      (DependentSimpleCategory.functor-equal C' p)
  ; functor-identity
    = λ x → dependent-functor-identity-unit
      (ChainCategory.functor-identity C x)
      (DependentSimpleCategory.functor-identity C' x)
  ; functor-compose
    = λ f g → dependent-functor-compose-unit
      (ChainCategory.functor-compose C f g)
      (DependentSimpleCategory.functor-compose C' f g)
  }

-- ### DependentFunctor

dependent-functor-unit {n = zero} F'
  = functor-unit F'

dependent-functor-unit {n = suc _} {F = F} F'
  = record
  { functor
    = λ x → dependent-functor-unit
      (DependentSimpleFunctor.functor F' x)
  ; functor-square
    = λ f → dependent-functor-square-unit
      (ChainFunctor.functor-square F f)
      (DependentSimpleFunctor.functor-square F' f)
  }

-- ### DependentFunctorEqual

dependent-functor-equal-unit {n = zero} _ p'
  = functor-equal-unit p'

dependent-functor-equal-unit {n = suc _} {D = D} {D' = D'} p p'
  = record
  { functor
    = λ x → dependent-functor-equal-unit'
      (ChainCategory.category' D)
      (DependentSimpleCategory.category D') 
      (ChainFunctorEqual.base p x)
      (ChainFunctorEqual.functor' p x)
      (DependentSimpleFunctorEqual.functor p' x)
  }

dependent-functor-equal-unit' _ _ refl
  = dependent-functor-equal-unit

-- ### DependentFunctorIdentity

dependent-functor-identity-unit {n = zero} _ p'
  = functor-identity-unit p'

dependent-functor-identity-unit {n = suc _} {C = C} {C' = C'} p p'
  = record
  { functor
    = λ x → dependent-functor-identity-unit'
      (ChainCategory.category' C)
      (DependentSimpleCategory.category C')
      (ChainFunctorIdentity.base p x)
      (ChainFunctorIdentity.functor' p x)
      (DependentSimpleFunctorIdentity.functor p' x)
  }

dependent-functor-identity-unit' _ _ refl
  = dependent-functor-identity-unit

-- ### DependentFunctorCompose

dependent-functor-compose-unit {n = zero} _ p'
  = functor-compose-unit p'

dependent-functor-compose-unit {n = suc _} {E = E} {E' = E'} p p'
  = record
  { functor
    = λ x → dependent-functor-compose-unit'
      (ChainCategory.category' E)
      (DependentSimpleCategory.category E')
      (ChainFunctorCompose.base p x)
      (ChainFunctorCompose.functor' p x)
      (DependentSimpleFunctorCompose.functor p' x)
  }

dependent-functor-compose-unit' _ _ refl
  = dependent-functor-compose-unit

-- ### DependentFunctorSquare

dependent-functor-square-unit {n = zero} _ s'
  = functor-square-unit s'

dependent-functor-square-unit {n = suc _} {D₂ = D₂} {D₂' = D₂'} s s'
  = record
  { functor
    = λ x₁ → dependent-functor-square-unit'
      (ChainCategory.category' D₂)
      (DependentSimpleCategory.category D₂')
      (ChainFunctorSquare.base s x₁)
      (ChainFunctorSquare.functor' s x₁)
      (DependentSimpleFunctorSquare.functor s' x₁)
  }

dependent-functor-square-unit' _ _ refl
  = dependent-functor-square-unit

