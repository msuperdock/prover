module Prover.Category.Dependent.Sigma.Maybe where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorIdentity;
    ChainFunctorSquare)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-maybe; functor-compose-sigma-maybe;
    functor-identity-sigma-maybe; functor-sigma-maybe;
    functor-square-sigma-maybe)
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

dependent-functor-identity-sigma-maybe-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁' : (x : A) → DependentCategory (C x))
  → (C₂' : (x : A) → DependentCategory (chain-category-snoc (C₁' x)))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F₁' : DependentFunctor (C₁' x₁) (C₁' x₂) F}
  → {F₂' : DependentFunctor (C₂' x₁) (C₂' x₂) (chain-functor-snoc F₁')}
  → x₂ ≡ x₁
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

dependent-functor-compose-sigma-maybe-eq
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
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F₁' : DependentFunctor D₁' (E₁' x₁) F}
  → {G₁' : DependentFunctor C₁' D₁' G}
  → {H₁' : DependentFunctor C₁' (E₁' x₂) H}
  → {F₂' : DependentFunctor D₂' (E₂' x₁) (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor C₂' D₂' (chain-functor-snoc G₁')}
  → {H₂' : DependentFunctor C₂' (E₂' x₂) (chain-functor-snoc H₁')}
  → x₂ ≡ x₁
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

dependent-functor-square-sigma-maybe-eq
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
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F₁' : DependentFunctor C₁₁' C₂₁' F}
  → {G₁' : DependentFunctor D₁₁' (D₂₁' x₁) G}
  → {H₁₁' : DependentFunctor C₁₁' D₁₁' H₁}
  → {H₂₁' : DependentFunctor C₂₁' (D₂₁' x₂) H₂}
  → {F₂' : DependentFunctor C₁₂' C₂₂' (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor D₁₂' (D₂₂' x₁) (chain-functor-snoc G₁')}
  → {H₁₂' : DependentFunctor C₁₂' D₁₂' (chain-functor-snoc H₁₁')}
  → {H₂₂' : DependentFunctor C₂₂' (D₂₂' x₂) (chain-functor-snoc H₂₁')}
  → x₂ ≡ x₁
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

-- ### DependentFunctorIdentity

dependent-functor-identity-sigma-maybe {n = zero} _ p₁' p₂'
  = functor-identity-sigma-maybe p₁' p₂'

dependent-functor-identity-sigma-maybe {n = suc _}
  {C = C} {C₁' = C₁'} {C₂' = C₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-identity-sigma-maybe-eq
      (ChainCategory.category' C)
      (DependentCategory.category C₁')
      (DependentCategory.category C₂')
      (ChainFunctorIdentity.base p x)
      (ChainFunctorIdentity.functor' p x)
      (DependentFunctorIdentity.functor p₁' x)
      (DependentFunctorIdentity.functor p₂' x)
  }

dependent-functor-identity-sigma-maybe-eq _ _ _ refl
  = dependent-functor-identity-sigma-maybe

-- ### DependentFunctorCompose

dependent-functor-compose-sigma-maybe {n = zero} _ p₁' p₂'
  = functor-compose-sigma-maybe p₁' p₂'

dependent-functor-compose-sigma-maybe {n = suc _}
  {E = E} {E₁' = E₁'} {E₂' = E₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-compose-sigma-maybe-eq
      (ChainCategory.category' E)
      (DependentCategory.category E₁')
      (DependentCategory.category E₂')
      (ChainFunctorCompose.base p x)
      (ChainFunctorCompose.functor' p x)
      (DependentFunctorCompose.functor p₁' x)
      (DependentFunctorCompose.functor p₂' x)
  }

dependent-functor-compose-sigma-maybe-eq _ _ _ refl
  = dependent-functor-compose-sigma-maybe

-- ### DependentFunctorSquare

dependent-functor-square-sigma-maybe {n = zero} _ s₁' s₂'
  = functor-square-sigma-maybe s₁' s₂'

dependent-functor-square-sigma-maybe {n = suc _}
  {D₂ = D₂} {D₂₁' = D₂₁'} {D₂₂' = D₂₂'} s s₁' s₂'
  = record
  { functor
    = λ x₁ → dependent-functor-square-sigma-maybe-eq
      (ChainCategory.category' D₂)
      (DependentCategory.category D₂₁')
      (DependentCategory.category D₂₂')
      (ChainFunctorSquare.base s x₁)
      (ChainFunctorSquare.functor' s x₁)
      (DependentFunctorSquare.functor s₁' x₁)
      (DependentFunctorSquare.functor s₂' x₁)
  }

dependent-functor-square-sigma-maybe-eq _ _ _ refl
  = dependent-functor-square-sigma-maybe

