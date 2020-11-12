module Prover.Category.Dependent.Product where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorEqual;
    ChainFunctorIdentity; ChainFunctorSquare)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorEqual; DependentFunctorIdentity; DependentFunctorSquare)
open import Prover.Category.Product
  using (category-product; functor-compose-product; functor-equal-product;
    functor-identity-product; functor-product; functor-square-product)
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

dependent-category-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → DependentCategory C
  → DependentCategory C

-- ### DependentFunctor

dependent-functor-product
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → {D₁' D₂' : DependentCategory D}
  → {F : ChainFunctor C D}
  → DependentFunctor C₁' D₁' F
  → DependentFunctor C₂' D₂' F
  → DependentFunctor
    (dependent-category-product C₁' C₂')
    (dependent-category-product D₁' D₂') F

-- ### DependentFunctorEqual

dependent-functor-equal-product
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → {D₁' D₂' : DependentCategory D}
  → {F₁ F₂ : ChainFunctor C D}
  → {F₁₁' : DependentFunctor C₁' D₁' F₁}
  → {F₁₂' : DependentFunctor C₁' D₁' F₂}
  → {F₂₁' : DependentFunctor C₂' D₂' F₁}
  → {F₂₂' : DependentFunctor C₂' D₂' F₂}
  → ChainFunctorEqual F₁ F₂
  → DependentFunctorEqual F₁₁' F₁₂'
  → DependentFunctorEqual F₂₁' F₂₂'
  → DependentFunctorEqual
    (dependent-functor-product F₁₁' F₂₁')
    (dependent-functor-product F₁₂' F₂₂')

dependent-functor-equal-product'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C : ChainCategory n}
  → (D : A → ChainCategory n)
  → {C₁' C₂' : DependentCategory C}
  → (D₁' D₂' : (x : A) → DependentCategory (D x))
  → {F₁ : ChainFunctor C (D x₁)}
  → {F₂ : ChainFunctor C (D x₂)}
  → {F₁₁' : DependentFunctor C₁' (D₁' x₁) F₁}
  → {F₁₂' : DependentFunctor C₁' (D₁' x₂) F₂}
  → {F₂₁' : DependentFunctor C₂' (D₂' x₁) F₁}
  → {F₂₂' : DependentFunctor C₂' (D₂' x₂) F₂}
  → x₁ ≡ x₂
  → ChainFunctorEqual F₁ F₂
  → DependentFunctorEqual F₁₁' F₁₂'
  → DependentFunctorEqual F₂₁' F₂₂'
  → DependentFunctorEqual
    (dependent-functor-product F₁₁' F₂₁')
    (dependent-functor-product F₁₂' F₂₂')

-- ### DependentFunctorIdentity

dependent-functor-identity-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → {F : ChainFunctor C C}
  → {F₁' : DependentFunctor C₁' C₁' F}
  → {F₂' : DependentFunctor C₂' C₂' F}
  → ChainFunctorIdentity F
  → DependentFunctorIdentity F₁'
  → DependentFunctorIdentity F₂'
  → DependentFunctorIdentity
    (dependent-functor-product F₁' F₂')

dependent-functor-identity-product'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁' C₂' : (x : A) → DependentCategory (C x))
  → {F : ChainFunctor (C x₂) (C x₁)}
  → {F₁' : DependentFunctor (C₁' x₂) (C₁' x₁) F}
  → {F₂' : DependentFunctor (C₂' x₂) (C₂' x₁) F}
  → x₁ ≡ x₂
  → ChainFunctorIdentity F
  → DependentFunctorIdentity F₁'
  → DependentFunctorIdentity F₂'
  → DependentFunctorIdentity
    (dependent-functor-product F₁' F₂')

-- ### DependentFunctorCompose

dependent-functor-compose-product
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → {D₁' D₂' : DependentCategory D}
  → {E₁' E₂' : DependentCategory E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F₁' : DependentFunctor D₁' E₁' F}
  → {F₂' : DependentFunctor D₂' E₂' F}
  → {G₁' : DependentFunctor C₁' D₁' G}
  → {G₂' : DependentFunctor C₂' D₂' G}
  → {H₁' : DependentFunctor C₁' E₁' H}
  → {H₂' : DependentFunctor C₂' E₂' H}
  → ChainFunctorCompose F G H
  → DependentFunctorCompose F₁' G₁' H₁'
  → DependentFunctorCompose F₂' G₂' H₂'
  → DependentFunctorCompose
    (dependent-functor-product F₁' F₂')
    (dependent-functor-product G₁' G₂')
    (dependent-functor-product H₁' H₂')

dependent-functor-compose-product'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C₁' C₂' : DependentCategory C}
  → {D₁' D₂' : DependentCategory D}
  → (E₁' E₂' : (x : A) → DependentCategory (E x))
  → {F : ChainFunctor D (E x₂)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₁)}
  → {F₁' : DependentFunctor D₁' (E₁' x₂) F}
  → {F₂' : DependentFunctor D₂' (E₂' x₂) F}
  → {G₁' : DependentFunctor C₁' D₁' G}
  → {G₂' : DependentFunctor C₂' D₂' G}
  → {H₁' : DependentFunctor C₁' (E₁' x₁) H}
  → {H₂' : DependentFunctor C₂' (E₂' x₁) H}
  → x₁ ≡ x₂
  → ChainFunctorCompose F G H
  → DependentFunctorCompose F₁' G₁' H₁'
  → DependentFunctorCompose F₂' G₂' H₂'
  → DependentFunctorCompose
    (dependent-functor-product F₁' F₂')
    (dependent-functor-product G₁' G₂')
    (dependent-functor-product H₁' H₂')

-- ### DependentFunctorSquare

dependent-functor-square-product
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C₁}
  → {C₁₂' C₂₂' : DependentCategory C₂}
  → {D₁₁' D₂₁' : DependentCategory D₁}
  → {D₁₂' D₂₂' : DependentCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F₁' : DependentFunctor C₁₁' C₁₂' F}
  → {F₂' : DependentFunctor C₂₁' C₂₂' F}
  → {G₁' : DependentFunctor D₁₁' D₁₂' G}
  → {G₂' : DependentFunctor D₂₁' D₂₂' G}
  → {H₁₁' : DependentFunctor C₁₁' D₁₁' H₁}
  → {H₂₁' : DependentFunctor C₂₁' D₂₁' H₁}
  → {H₁₂' : DependentFunctor C₁₂' D₁₂' H₂}
  → {H₂₂' : DependentFunctor C₂₂' D₂₂' H₂}
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F₁' G₁' H₁₁' H₁₂'
  → DependentFunctorSquare F₂' G₂' H₂₁' H₂₂'
  → DependentFunctorSquare
    (dependent-functor-product F₁' F₂')
    (dependent-functor-product G₁' G₂')
    (dependent-functor-product H₁₁' H₂₁')
    (dependent-functor-product H₁₂' H₂₂')

dependent-functor-square-product'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁₁' C₂₁' : DependentCategory C₁}
  → {C₁₂' C₂₂' : DependentCategory C₂}
  → {D₁₁' D₂₁' : DependentCategory D₁}
  → (D₁₂' D₂₂' : (x : A) → DependentCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₂)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₁)}
  → {F₁' : DependentFunctor C₁₁' C₁₂' F}
  → {F₂' : DependentFunctor C₂₁' C₂₂' F}
  → {G₁' : DependentFunctor D₁₁' (D₁₂' x₂) G}
  → {G₂' : DependentFunctor D₂₁' (D₂₂' x₂) G}
  → {H₁₁' : DependentFunctor C₁₁' D₁₁' H₁}
  → {H₁₂' : DependentFunctor C₁₂' (D₁₂' x₁) H₂}
  → {H₂₁' : DependentFunctor C₂₁' D₂₁' H₁}
  → {H₂₂' : DependentFunctor C₂₂' (D₂₂' x₁) H₂}
  → x₁ ≡ x₂
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F₁' G₁' H₁₁' H₁₂'
  → DependentFunctorSquare F₂' G₂' H₂₁' H₂₂'
  → DependentFunctorSquare
    (dependent-functor-product F₁' F₂')
    (dependent-functor-product G₁' G₂')
    (dependent-functor-product H₁₁' H₂₁')
    (dependent-functor-product H₁₂' H₂₂')

-- ## Definitions

-- ### DependentCategory

dependent-category-product {n = zero} C₁' C₂'
  = category-product C₁' C₂'

dependent-category-product {n = suc _} {C = C} C₁' C₂'
  = record
  { category
    = λ x → dependent-category-product
      (DependentCategory.category C₁' x)
      (DependentCategory.category C₂' x)
  ; functor
    = λ f → dependent-functor-product
      (DependentCategory.functor C₁' f)
      (DependentCategory.functor C₂' f)
  ; functor-equal
    = λ p → dependent-functor-equal-product
      (ChainCategory.functor-equal C p)
      (DependentCategory.functor-equal C₁' p)
      (DependentCategory.functor-equal C₂' p)
  ; functor-identity
    = λ x → dependent-functor-identity-product
      (ChainCategory.functor-identity C x)
      (DependentCategory.functor-identity C₁' x)
      (DependentCategory.functor-identity C₂' x)
  ; functor-compose
    = λ f g → dependent-functor-compose-product
      (ChainCategory.functor-compose C f g)
      (DependentCategory.functor-compose C₁' f g)
      (DependentCategory.functor-compose C₂' f g)
  }

-- ### DependentFunctor

dependent-functor-product {n = zero} F₁' F₂'
  = functor-product F₁' F₂'

dependent-functor-product {n = suc _} {F = F} F₁' F₂'
  = record
  { functor
    = λ x → dependent-functor-product
      (DependentFunctor.functor F₁' x)
      (DependentFunctor.functor F₂' x)
  ; functor-square
    = λ f → dependent-functor-square-product
      (ChainFunctor.functor-square F f)
      (DependentFunctor.functor-square F₁' f)
      (DependentFunctor.functor-square F₂' f)
  }

-- ### DependentFunctorEqual

dependent-functor-equal-product {n = zero} _ p₁' p₂'
  = functor-equal-product p₁' p₂'

dependent-functor-equal-product {n = suc _}
  {D = D} {D₁' = D₁'} {D₂' = D₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-equal-product'
      (ChainCategory.category' D)
      (DependentCategory.category D₁')
      (DependentCategory.category D₂')
      (ChainFunctorEqual.base p x)
      (ChainFunctorEqual.functor' p x)
      (DependentFunctorEqual.functor p₁' x)
      (DependentFunctorEqual.functor p₂' x)
  }

dependent-functor-equal-product' _ _ _ refl
  = dependent-functor-equal-product

-- ### DependentFunctorIdentity

dependent-functor-identity-product {n = zero} _ p₁' p₂'
  = functor-identity-product p₁' p₂'

dependent-functor-identity-product {n = suc _}
  {C = C} {C₁' = C₁'} {C₂' = C₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-identity-product'
      (ChainCategory.category' C)
      (DependentCategory.category C₁')
      (DependentCategory.category C₂')
      (ChainFunctorIdentity.base p x)
      (ChainFunctorIdentity.functor' p x)
      (DependentFunctorIdentity.functor p₁' x)
      (DependentFunctorIdentity.functor p₂' x)
  }

dependent-functor-identity-product' _ _ _ refl
  = dependent-functor-identity-product

-- ### DependentFunctorCompose

dependent-functor-compose-product {n = zero} _ p₁' p₂'
  = functor-compose-product p₁' p₂'

dependent-functor-compose-product {n = suc _}
  {E = E} {E₁' = E₁'} {E₂' = E₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-compose-product'
      (ChainCategory.category' E)
      (DependentCategory.category E₁')
      (DependentCategory.category E₂')
      (ChainFunctorCompose.base p x)
      (ChainFunctorCompose.functor' p x)
      (DependentFunctorCompose.functor p₁' x)
      (DependentFunctorCompose.functor p₂' x)
  }

dependent-functor-compose-product' _ _ _ refl
  = dependent-functor-compose-product

-- ### DependentFunctorSquare

dependent-functor-square-product {n = zero} _ s₁' s₂'
  = functor-square-product s₁' s₂'

dependent-functor-square-product {n = suc _}
  {D₂ = D₂} {D₁₂' = D₁₂'} {D₂₂' = D₂₂'} s s₁' s₂'
  = record
  { functor
    = λ x₁ → dependent-functor-square-product'
      (ChainCategory.category' D₂)
      (DependentCategory.category D₁₂')
      (DependentCategory.category D₂₂')
      (ChainFunctorSquare.base s x₁)
      (ChainFunctorSquare.functor' s x₁)
      (DependentFunctorSquare.functor s₁' x₁)
      (DependentFunctorSquare.functor s₂' x₁)
  }

dependent-functor-square-product' _ _ _ refl
  = dependent-functor-square-product

