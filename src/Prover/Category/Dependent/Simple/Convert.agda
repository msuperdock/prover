module Prover.Category.Dependent.Simple.Convert where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare)
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
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

dependent-category-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → DependentSimpleCategory C

-- ### DependentFunctor

dependent-functor-simple
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {F : ChainFunctor C D}
  → DependentFunctor C' D' F
  → DependentSimpleFunctor
    (dependent-category-simple C')
    (dependent-category-simple D') F

-- ### DependentFunctorEqual

dependent-functor-equal-simple
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {F₁ F₂ : ChainFunctor C D}
  → {F₁' : DependentFunctor C' D' F₁}
  → {F₂' : DependentFunctor C' D' F₂}
  → ChainFunctorEqual F₁ F₂
  → DependentFunctorEqual F₁' F₂'
  → DependentSimpleFunctorEqual
    (dependent-functor-simple F₁')
    (dependent-functor-simple F₂')

dependent-functor-equal-simple'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C : ChainCategory n}
  → (D : A → ChainCategory n)
  → {C' : DependentCategory C}
  → (D' : (x : A) → DependentCategory (D x))
  → {F₁ : ChainFunctor C (D x₁)}
  → {F₂ : ChainFunctor C (D x₂)}
  → {F₁' : DependentFunctor C' (D' x₁) F₁}
  → {F₂' : DependentFunctor C' (D' x₂) F₂}
  → x₁ ≡ x₂
  → ChainFunctorEqual F₁ F₂
  → DependentFunctorEqual F₁' F₂'
  → DependentSimpleFunctorEqual
    (dependent-functor-simple F₁')
    (dependent-functor-simple F₂')

-- ### DependentFunctorIdentity

dependent-functor-identity-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {F : ChainFunctor C C}
  → {F' : DependentFunctor C' C' F}
  → ChainFunctorIdentity F
  → DependentFunctorIdentity F'
  → DependentSimpleFunctorIdentity
    (dependent-functor-simple F')

dependent-functor-identity-simple'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → DependentCategory (C x))
  → {F : ChainFunctor (C x₂) (C x₁)}
  → {F' : DependentFunctor (C' x₂) (C' x₁) F}
  → x₁ ≡ x₂
  → ChainFunctorIdentity F
  → DependentFunctorIdentity F'
  → DependentSimpleFunctorIdentity
    (dependent-functor-simple F')

-- ### DependentFunctorCompose

dependent-functor-compose-simple
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {E' : DependentCategory E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : DependentFunctor D' E' F}
  → {G' : DependentFunctor C' D' G}
  → {H' : DependentFunctor C' E' H}
  → ChainFunctorCompose F G H
  → DependentFunctorCompose F' G' H'
  → DependentSimpleFunctorCompose
    (dependent-functor-simple F')
    (dependent-functor-simple G')
    (dependent-functor-simple H')

dependent-functor-compose-simple'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → (E' : (x : A) → DependentCategory (E x))
  → {F : ChainFunctor D (E x₂)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₁)}
  → {F' : DependentFunctor D' (E' x₂) F}
  → {G' : DependentFunctor C' D' G}
  → {H' : DependentFunctor C' (E' x₁) H}
  → x₁ ≡ x₂
  → ChainFunctorCompose F G H
  → DependentFunctorCompose F' G' H'
  → DependentSimpleFunctorCompose
    (dependent-functor-simple F')
    (dependent-functor-simple G')
    (dependent-functor-simple H')

-- ### DependentFunctorSquare

dependent-functor-square-simple
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {D₁' : DependentCategory D₁}
  → {D₂' : DependentCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' D₂' G}
  → {H₁' : DependentFunctor C₁' D₁' H₁}
  → {H₂' : DependentFunctor C₂' D₂' H₂}
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F' G' H₁' H₂'
  → DependentSimpleFunctorSquare
    (dependent-functor-simple F')
    (dependent-functor-simple G')
    (dependent-functor-simple H₁')
    (dependent-functor-simple H₂')

dependent-functor-square-simple'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {D₁' : DependentCategory D₁}
  → (D₂' : (x : A) → DependentCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₂)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₁)}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' (D₂' x₂) G}
  → {H₁' : DependentFunctor C₁' D₁' H₁}
  → {H₂' : DependentFunctor C₂' (D₂' x₁) H₂}
  → x₁ ≡ x₂
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F' G' H₁' H₂'
  → DependentSimpleFunctorSquare
    (dependent-functor-simple F')
    (dependent-functor-simple G')
    (dependent-functor-simple H₁')
    (dependent-functor-simple H₂')

-- ## Definitions

-- ### DependentCategory

dependent-category-simple {n = zero} C'
  = Category.Object C'

dependent-category-simple {n = suc _} {C = C} C'
  = record
  { category
    = λ x → dependent-category-simple
      (DependentCategory.category C' x)
  ; functor
    = λ f → dependent-functor-simple
      (DependentCategory.functor C' f)
  ; functor-equal
    = λ p → dependent-functor-equal-simple
      (ChainCategory.functor-equal C p)
      (DependentCategory.functor-equal C' p)
  ; functor-identity
    = λ x → dependent-functor-identity-simple
      (ChainCategory.functor-identity C x)
      (DependentCategory.functor-identity C' x)
  ; functor-compose
    = λ f g → dependent-functor-compose-simple
      (ChainCategory.functor-compose C f g)
      (DependentCategory.functor-compose C' f g)
  }

-- ### DependentFunctor

dependent-functor-simple {n = zero} F'
  = Functor.function F'

dependent-functor-simple {n = suc _} {F = F} F'
  = record
  { functor
    = λ x → dependent-functor-simple
      (DependentFunctor.functor F' x)
  ; functor-square
    = λ f → dependent-functor-square-simple
      (ChainFunctor.functor-square F f)
      (DependentFunctor.functor-square F' f)
  }

-- ### DependentFunctorEqual

dependent-functor-equal-simple {n = zero} _ p'
  = FunctorEqual.function p'

dependent-functor-equal-simple {n = suc _} {D = D} {D' = D'} p p'
  = record
  { functor
    = λ x → dependent-functor-equal-simple'
      (ChainCategory.category' D)
      (DependentCategory.category D')
      (ChainFunctorEqual.base p x)
      (ChainFunctorEqual.functor' p x)
      (DependentFunctorEqual.functor p' x)
  }

dependent-functor-equal-simple' _ _ refl
  = dependent-functor-equal-simple

-- ### DependentFunctorIdentity

dependent-functor-identity-simple {n = zero} _ p'
  = FunctorIdentity.function p'

dependent-functor-identity-simple {n = suc _} {C = C} {C' = C'} p p'
  = record
  { functor
    = λ x → dependent-functor-identity-simple'
      (ChainCategory.category' C)
      (DependentCategory.category C')
      (ChainFunctorIdentity.base p x)
      (ChainFunctorIdentity.functor' p x)
      (DependentFunctorIdentity.functor p' x)
  }

dependent-functor-identity-simple' _ _ refl
  = dependent-functor-identity-simple

-- ### DependentFunctorCompose

dependent-functor-compose-simple {n = zero} _ p'
  = FunctorCompose.function p'

dependent-functor-compose-simple {n = suc _} {E = E} {E' = E'} p p'
  = record
  { functor
    = λ x → dependent-functor-compose-simple'
      (ChainCategory.category' E)
      (DependentCategory.category E')
      (ChainFunctorCompose.base p x)
      (ChainFunctorCompose.functor' p x)
      (DependentFunctorCompose.functor p' x)
  }

dependent-functor-compose-simple' _ _ refl
  = dependent-functor-compose-simple

-- ### DependentFunctorSquare

dependent-functor-square-simple {n = zero} _ s'
  = FunctorSquare.function s'

dependent-functor-square-simple {n = suc _} {D₂ = D₂} {D₂' = D₂'} s s'
  = record
  { functor
    = λ x₁ → dependent-functor-square-simple'
      (ChainCategory.category' D₂)
      (DependentCategory.category D₂')
      (ChainFunctorSquare.base s x₁)
      (ChainFunctorSquare.functor' s x₁)
      (DependentFunctorSquare.functor s' x₁)
  }

dependent-functor-square-simple' _ _ refl
  = dependent-functor-square-simple

