module Prover.Category.Snoc where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorEqual;
    ChainFunctorIdentity; ChainFunctorSquare; chain₁-category; chain₁-functor;
    chain₁-functor-compose; chain₁-functor-equal; chain₁-functor-identity;
    chain₁-functor-square)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorEqual; DependentFunctorIdentity; DependentFunctorSquare)
open import Prover.Prelude

-- ## Types

-- ### ChainCategory

chain-category-snoc
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → ChainCategory (suc n)

-- ### ChainFunctor

chain-functor-snoc
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {F : ChainFunctor C D}
  → DependentFunctor C' D' F
  → ChainFunctor
    (chain-category-snoc C')
    (chain-category-snoc D')

-- ### ChainFunctorEqual

chain-functor-equal-snoc
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {F₁ F₂ : ChainFunctor C D}
  → {F₁' : DependentFunctor C' D' F₁}
  → {F₂' : DependentFunctor C' D' F₂}
  → ChainFunctorEqual F₁ F₂
  → DependentFunctorEqual F₁' F₂'
  → ChainFunctorEqual
    (chain-functor-snoc F₁')
    (chain-functor-snoc F₂')

chain-functor-equal-snoc'
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
  → ChainFunctorEqual
    (chain-functor-snoc F₁')
    (chain-functor-snoc F₂')

-- ### ChainFunctorIdentity

chain-functor-identity-snoc
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {F : ChainFunctor C C}
  → {F' : DependentFunctor C' C' F}
  → ChainFunctorIdentity F
  → DependentFunctorIdentity F'
  → ChainFunctorIdentity
    (chain-functor-snoc F')

chain-functor-identity-snoc'
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
  → ChainFunctorIdentity
    (chain-functor-snoc F')

-- ### ChainFunctorCompose

chain-functor-compose-snoc
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
  → ChainFunctorCompose
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H')

chain-functor-compose-snoc'
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
  → ChainFunctorCompose
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H')

-- ### ChainFunctorSquare

chain-functor-square-snoc
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
  → ChainFunctorSquare
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H₁')
    (chain-functor-snoc H₂')

chain-functor-square-snoc'
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
  → ChainFunctorSquare
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H₁')
    (chain-functor-snoc H₂')

-- ## Definitions

-- ### ChainCategory

chain-category-snoc {n = zero} C'
  = chain₁-category C'

chain-category-snoc {n = suc _} {C = C} C'
  = record
  { category
    = ChainCategory.category C
  ; category'
    = λ x → chain-category-snoc
      (DependentCategory.category C' x)
  ; functor
    = λ f → chain-functor-snoc
      (DependentCategory.functor C' f)
  ; functor-equal
    = λ p → chain-functor-equal-snoc
      (ChainCategory.functor-equal C p)
      (DependentCategory.functor-equal C' p)
  ; functor-identity
    = λ x → chain-functor-identity-snoc
      (ChainCategory.functor-identity C x)
      (DependentCategory.functor-identity C' x)
  ; functor-compose
    = λ f g → chain-functor-compose-snoc
      (ChainCategory.functor-compose C f g)
      (DependentCategory.functor-compose C' f g)
  }

-- ### ChainFunctor

chain-functor-snoc {n = zero} F'
  = chain₁-functor F'

chain-functor-snoc {n = suc _} {F = F} F'
  = record
  { functor
    = ChainFunctor.functor F
  ; functor'
    = λ x → chain-functor-snoc
      (DependentFunctor.functor F' x)
  ; functor-square
    = λ f → chain-functor-square-snoc
      (ChainFunctor.functor-square F f)
      (DependentFunctor.functor-square F' f)
  }

-- ### ChainFunctorEqual

chain-functor-equal-snoc {n = zero} _ p'
  = chain₁-functor-equal p'

chain-functor-equal-snoc {n = suc _} {D = D} {D' = D'} p p'
  = record
  { functor
    = ChainFunctorEqual.functor p
  ; functor'
    = λ x → chain-functor-equal-snoc'
      (ChainCategory.category' D)
      (DependentCategory.category D')
      (ChainFunctorEqual.base p x)
      (ChainFunctorEqual.functor' p x)
      (DependentFunctorEqual.functor p' x)
  }

chain-functor-equal-snoc' _ _ refl
  = chain-functor-equal-snoc

-- ### ChainFunctorIdentity

chain-functor-identity-snoc {n = zero} _ p'
  = chain₁-functor-identity p'

chain-functor-identity-snoc {n = suc _} {C = C} {C' = C'} p p'
  = record
  { functor
    = ChainFunctorIdentity.functor p
  ; functor'
    = λ x → chain-functor-identity-snoc'
      (ChainCategory.category' C)
      (DependentCategory.category C')
      (ChainFunctorIdentity.base p x)
      (ChainFunctorIdentity.functor' p x)
      (DependentFunctorIdentity.functor p' x)
  }

chain-functor-identity-snoc' _ _ refl
  = chain-functor-identity-snoc

-- ### ChainFunctorCompose

chain-functor-compose-snoc {n = zero} _ p'
  = chain₁-functor-compose p'

chain-functor-compose-snoc {n = suc _} {E = E} {E' = E'} p p'
  = record
  { functor
    = ChainFunctorCompose.functor p
  ; functor'
    = λ x → chain-functor-compose-snoc'
      (ChainCategory.category' E)
      (DependentCategory.category E')
      (ChainFunctorCompose.base p x)
      (ChainFunctorCompose.functor' p x)
      (DependentFunctorCompose.functor p' x)
  }

chain-functor-compose-snoc' _ _ refl
  = chain-functor-compose-snoc

-- ### ChainFunctorSquare

chain-functor-square-snoc {n = zero} _ s'
  = chain₁-functor-square s'

chain-functor-square-snoc {n = suc _} {D₂ = D₂} {D₂' = D₂'} s s'
  = record
  { functor
    = ChainFunctorSquare.functor s
  ; functor'
    = λ x₁ → chain-functor-square-snoc'
      (ChainCategory.category' D₂)
      (DependentCategory.category D₂')
      (ChainFunctorSquare.base s x₁)
      (ChainFunctorSquare.functor' s x₁)
      (DependentFunctorSquare.functor s' x₁)
  }

chain-functor-square-snoc' _ _ refl
  = chain-functor-square-snoc

