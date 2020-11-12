module Prover.Category.Dependent.Sigma.Maybe where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorEqual;
    ChainFunctorIdentity; ChainFunctorSquare)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorEqual; DependentFunctorIdentity; DependentFunctorSquare)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-maybe; functor-compose-sigma-maybe;
    functor-equal-sigma-maybe; functor-identity-sigma-maybe;
    functor-sigma-maybe; functor-square-sigma-maybe)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-functor-snoc)
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

dependent-category-sigma-maybe
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : DependentCategory C)
  → DependentCategory (chain-category-snoc C₁')
  → DependentCategory C

-- ### DependentFunctor

dependent-functor-sigma-maybe
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {D₁' : DependentCategory D}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → {D₂' : DependentCategory (chain-category-snoc D₁')}
  → {F : ChainFunctor C D}
  → (F₁' : DependentFunctor C₁' D₁' F)
  → DependentFunctor C₂' D₂' (chain-functor-snoc F₁')
  → DependentFunctor
    (dependent-category-sigma-maybe C₁' C₂')
    (dependent-category-sigma-maybe D₁' D₂') F

-- ### DependentFunctorEqual

dependent-functor-equal-sigma-maybe
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {D₁' : DependentCategory D}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → {D₂' : DependentCategory (chain-category-snoc D₁')}
  → {F₁ F₂ : ChainFunctor C D}
  → {F₁₁' : DependentFunctor C₁' D₁' F₁}
  → {F₂₁' : DependentFunctor C₁' D₁' F₂}
  → {F₁₂' : DependentFunctor C₂' D₂' (chain-functor-snoc F₁₁')}
  → {F₂₂' : DependentFunctor C₂' D₂' (chain-functor-snoc F₂₁')}
  → ChainFunctorEqual F₁ F₂
  → DependentFunctorEqual F₁₁' F₂₁'
  → DependentFunctorEqual F₁₂' F₂₂'
  → DependentFunctorEqual
    (dependent-functor-sigma-maybe F₁₁' F₁₂')
    (dependent-functor-sigma-maybe F₂₁' F₂₂')

dependent-functor-equal-sigma-maybe'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C : ChainCategory n}
  → (D : A → ChainCategory n)
  → {C₁' : DependentCategory C}
  → (D₁' : (x : A) → DependentCategory (D x))
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → (D₂' : (x : A) → DependentCategory (chain-category-snoc (D₁' x)))
  → {F₁ : ChainFunctor C (D x₁)}
  → {F₂ : ChainFunctor C (D x₂)}
  → {F₁₁' : DependentFunctor C₁' (D₁' x₁) F₁}
  → {F₂₁' : DependentFunctor C₁' (D₁' x₂) F₂}
  → {F₁₂' : DependentFunctor C₂' (D₂' x₁) (chain-functor-snoc F₁₁')}
  → {F₂₂' : DependentFunctor C₂' (D₂' x₂) (chain-functor-snoc F₂₁')}
  → x₁ ≡ x₂
  → ChainFunctorEqual F₁ F₂
  → DependentFunctorEqual F₁₁' F₂₁'
  → DependentFunctorEqual F₁₂' F₂₂'
  → DependentFunctorEqual
    (dependent-functor-sigma-maybe F₁₁' F₁₂')
    (dependent-functor-sigma-maybe F₂₁' F₂₂')

-- ### DependentFunctorIdentity

dependent-functor-identity-sigma-maybe
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → {F : ChainFunctor C C}
  → {F₁' : DependentFunctor C₁' C₁' F}
  → {F₂' : DependentFunctor C₂' C₂' (chain-functor-snoc F₁')}
  → ChainFunctorIdentity F 
  → DependentFunctorIdentity F₁'
  → DependentFunctorIdentity F₂'
  → DependentFunctorIdentity
    (dependent-functor-sigma-maybe F₁' F₂')

dependent-functor-identity-sigma-maybe'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁' : (x : A) → DependentCategory (C x))
  → (C₂' : (x : A) → DependentCategory (chain-category-snoc (C₁' x)))
  → {F : ChainFunctor (C x₂) (C x₁)}
  → {F₁' : DependentFunctor (C₁' x₂) (C₁' x₁) F}
  → {F₂' : DependentFunctor (C₂' x₂) (C₂' x₁) (chain-functor-snoc F₁')}
  → x₁ ≡ x₂
  → ChainFunctorIdentity F 
  → DependentFunctorIdentity F₁'
  → DependentFunctorIdentity F₂'
  → DependentFunctorIdentity
    (dependent-functor-sigma-maybe F₁' F₂')

-- ### DependentFunctorCompose

dependent-functor-compose-sigma-maybe
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {D₁' : DependentCategory D}
  → {E₁' : DependentCategory E}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → {D₂' : DependentCategory (chain-category-snoc D₁')}
  → {E₂' : DependentCategory (chain-category-snoc E₁')}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F₁' : DependentFunctor D₁' E₁' F}
  → {G₁' : DependentFunctor C₁' D₁' G}
  → {H₁' : DependentFunctor C₁' E₁' H}
  → {F₂' : DependentFunctor D₂' E₂' (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor C₂' D₂' (chain-functor-snoc G₁')}
  → {H₂' : DependentFunctor C₂' E₂' (chain-functor-snoc H₁')}
  → ChainFunctorCompose F G H
  → DependentFunctorCompose F₁' G₁' H₁'
  → DependentFunctorCompose F₂' G₂' H₂'
  → DependentFunctorCompose
    (dependent-functor-sigma-maybe F₁' F₂')
    (dependent-functor-sigma-maybe G₁' G₂')
    (dependent-functor-sigma-maybe H₁' H₂')

dependent-functor-compose-sigma-maybe'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C₁' : DependentCategory C}
  → {D₁' : DependentCategory D}
  → (E₁' : (x : A) → DependentCategory (E x))
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → {D₂' : DependentCategory (chain-category-snoc D₁')}
  → (E₂' : (x : A) → DependentCategory (chain-category-snoc (E₁' x)))
  → {F : ChainFunctor D (E x₂)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₁)}
  → {F₁' : DependentFunctor D₁' (E₁' x₂) F}
  → {G₁' : DependentFunctor C₁' D₁' G}
  → {H₁' : DependentFunctor C₁' (E₁' x₁) H}
  → {F₂' : DependentFunctor D₂' (E₂' x₂) (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor C₂' D₂' (chain-functor-snoc G₁')}
  → {H₂' : DependentFunctor C₂' (E₂' x₁) (chain-functor-snoc H₁')}
  → x₁ ≡ x₂
  → ChainFunctorCompose F G H
  → DependentFunctorCompose F₁' G₁' H₁'
  → DependentFunctorCompose F₂' G₂' H₂'
  → DependentFunctorCompose
    (dependent-functor-sigma-maybe F₁' F₂')
    (dependent-functor-sigma-maybe G₁' G₂')
    (dependent-functor-sigma-maybe H₁' H₂')

-- ### DependentFunctorSquare

dependent-functor-square-sigma-maybe
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁₁' : DependentCategory C₁}
  → {C₂₁' : DependentCategory C₂}
  → {D₁₁' : DependentCategory D₁}
  → {D₂₁' : DependentCategory D₂}
  → {C₁₂' : DependentCategory (chain-category-snoc C₁₁')}
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → {D₁₂' : DependentCategory (chain-category-snoc D₁₁')}
  → {D₂₂' : DependentCategory (chain-category-snoc D₂₁')}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F₁' : DependentFunctor C₁₁' C₂₁' F}
  → {G₁' : DependentFunctor D₁₁' D₂₁' G}
  → {H₁₁' : DependentFunctor C₁₁' D₁₁' H₁}
  → {H₂₁' : DependentFunctor C₂₁' D₂₁' H₂}
  → {F₂' : DependentFunctor C₁₂' C₂₂' (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor D₁₂' D₂₂' (chain-functor-snoc G₁')}
  → {H₁₂' : DependentFunctor C₁₂' D₁₂' (chain-functor-snoc H₁₁')}
  → {H₂₂' : DependentFunctor C₂₂' D₂₂' (chain-functor-snoc H₂₁')}
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F₁' G₁' H₁₁' H₂₁'
  → DependentFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → DependentFunctorSquare
    (dependent-functor-sigma-maybe F₁' F₂')
    (dependent-functor-sigma-maybe G₁' G₂')
    (dependent-functor-sigma-maybe H₁₁' H₁₂')
    (dependent-functor-sigma-maybe H₂₁' H₂₂')

dependent-functor-square-sigma-maybe'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁₁' : DependentCategory C₁}
  → {C₂₁' : DependentCategory C₂}
  → {D₁₁' : DependentCategory D₁}
  → (D₂₁' : (x : A) → DependentCategory (D₂ x))
  → {C₁₂' : DependentCategory (chain-category-snoc C₁₁')}
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → {D₁₂' : DependentCategory (chain-category-snoc D₁₁')}
  → (D₂₂' : (x : A) → DependentCategory (chain-category-snoc (D₂₁' x)))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₂)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₁)}
  → {F₁' : DependentFunctor C₁₁' C₂₁' F}
  → {G₁' : DependentFunctor D₁₁' (D₂₁' x₂) G}
  → {H₁₁' : DependentFunctor C₁₁' D₁₁' H₁}
  → {H₂₁' : DependentFunctor C₂₁' (D₂₁' x₁) H₂}
  → {F₂' : DependentFunctor C₁₂' C₂₂' (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor D₁₂' (D₂₂' x₂) (chain-functor-snoc G₁')}
  → {H₁₂' : DependentFunctor C₁₂' D₁₂' (chain-functor-snoc H₁₁')}
  → {H₂₂' : DependentFunctor C₂₂' (D₂₂' x₁) (chain-functor-snoc H₂₁')}
  → x₁ ≡ x₂
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F₁' G₁' H₁₁' H₂₁'
  → DependentFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → DependentFunctorSquare
    (dependent-functor-sigma-maybe F₁' F₂')
    (dependent-functor-sigma-maybe G₁' G₂')
    (dependent-functor-sigma-maybe H₁₁' H₁₂')
    (dependent-functor-sigma-maybe H₂₁' H₂₂')

-- ## Definitions

-- ### DependentCategory

dependent-category-sigma-maybe {n = zero} _ C₂'
  = category-sigma-maybe C₂'

dependent-category-sigma-maybe {n = suc _} {C = C} C₁' C₂'
  = record
  { category
    = λ x → dependent-category-sigma-maybe
      (DependentCategory.category C₁' x)
      (DependentCategory.category C₂' x)
  ; functor
    = λ f → dependent-functor-sigma-maybe
      (DependentCategory.functor C₁' f)
      (DependentCategory.functor C₂' f)
  ; functor-equal
    = λ p → dependent-functor-equal-sigma-maybe
      (ChainCategory.functor-equal C p)
      (DependentCategory.functor-equal C₁' p)
      (DependentCategory.functor-equal C₂' p)
  ; functor-identity
    = λ x → dependent-functor-identity-sigma-maybe
      (ChainCategory.functor-identity C x)
      (DependentCategory.functor-identity C₁' x)
      (DependentCategory.functor-identity C₂' x)
  ; functor-compose
    = λ f g → dependent-functor-compose-sigma-maybe
      (ChainCategory.functor-compose C f g)
      (DependentCategory.functor-compose C₁' f g)
      (DependentCategory.functor-compose C₂' f g)
  }

-- ### DependentFunctor

dependent-functor-sigma-maybe {n = zero} _ F₂'
  = functor-sigma-maybe F₂'

dependent-functor-sigma-maybe {n = suc _} {F = F} F₁' F₂'
  = record
  { functor
    = λ x → dependent-functor-sigma-maybe
      (DependentFunctor.functor F₁' x)
      (DependentFunctor.functor F₂' x)
  ; functor-square
    = λ f → dependent-functor-square-sigma-maybe
      (ChainFunctor.functor-square F f)
      (DependentFunctor.functor-square F₁' f)
      (DependentFunctor.functor-square F₂' f)
  }

-- ### DependentFunctorEqual

dependent-functor-equal-sigma-maybe {n = zero} _ p₁' p₂'
  = functor-equal-sigma-maybe p₁' p₂'

dependent-functor-equal-sigma-maybe {n = suc _}
  {D = D} {D₁' = D₁'} {D₂' = D₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-equal-sigma-maybe'
      (ChainCategory.category' D)
      (DependentCategory.category D₁')
      (DependentCategory.category D₂')
      (ChainFunctorEqual.base p x)
      (ChainFunctorEqual.functor' p x)
      (DependentFunctorEqual.functor p₁' x)
      (DependentFunctorEqual.functor p₂' x)
  }

dependent-functor-equal-sigma-maybe' _ _ _ refl
  = dependent-functor-equal-sigma-maybe

-- ### DependentFunctorIdentity

dependent-functor-identity-sigma-maybe {n = zero} _ p₁' p₂'
  = functor-identity-sigma-maybe p₁' p₂'

dependent-functor-identity-sigma-maybe {n = suc _}
  {C = C} {C₁' = C₁'} {C₂' = C₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-identity-sigma-maybe'
      (ChainCategory.category' C)
      (DependentCategory.category C₁')
      (DependentCategory.category C₂')
      (ChainFunctorIdentity.base p x)
      (ChainFunctorIdentity.functor' p x)
      (DependentFunctorIdentity.functor p₁' x)
      (DependentFunctorIdentity.functor p₂' x)
  }

dependent-functor-identity-sigma-maybe' _ _ _ refl
  = dependent-functor-identity-sigma-maybe

-- ### DependentFunctorCompose

dependent-functor-compose-sigma-maybe {n = zero} _ p₁' p₂'
  = functor-compose-sigma-maybe p₁' p₂'

dependent-functor-compose-sigma-maybe {n = suc _}
  {E = E} {E₁' = E₁'} {E₂' = E₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-compose-sigma-maybe'
      (ChainCategory.category' E)
      (DependentCategory.category E₁')
      (DependentCategory.category E₂')
      (ChainFunctorCompose.base p x)
      (ChainFunctorCompose.functor' p x)
      (DependentFunctorCompose.functor p₁' x)
      (DependentFunctorCompose.functor p₂' x)
  }

dependent-functor-compose-sigma-maybe' _ _ _ refl
  = dependent-functor-compose-sigma-maybe

-- ### DependentFunctorSquare

dependent-functor-square-sigma-maybe {n = zero} _ s₁' s₂'
  = functor-square-sigma-maybe s₁' s₂'

dependent-functor-square-sigma-maybe {n = suc _}
  {D₂ = D₂} {D₂₁' = D₂₁'} {D₂₂' = D₂₂'} s s₁' s₂'
  = record
  { functor
    = λ x₁ → dependent-functor-square-sigma-maybe'
      (ChainCategory.category' D₂)
      (DependentCategory.category D₂₁')
      (DependentCategory.category D₂₂')
      (ChainFunctorSquare.base s x₁)
      (ChainFunctorSquare.functor' s x₁)
      (DependentFunctorSquare.functor s₁' x₁)
      (DependentFunctorSquare.functor s₂' x₁)
  }

dependent-functor-square-sigma-maybe' _ _ _ refl
  = dependent-functor-square-sigma-maybe

