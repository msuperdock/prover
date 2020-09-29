module Prover.Category.Dependent.Product where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorIdentity;
    ChainFunctorSquare)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare)
open import Prover.Category.Product
  using (category-product; functor-compose-product; functor-identity-product;
    functor-product; functor-square-product)
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

dependent-functor-identity-product-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁' C₂' : (x : A) → DependentCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F₁' : DependentFunctor (C₁' x₁) (C₁' x₂) F}
  → {F₂' : DependentFunctor (C₂' x₁) (C₂' x₂) F}
  → x₂ ≡ x₁
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

dependent-functor-compose-product-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C₁' C₂' : DependentCategory C}
  → {D₁' D₂' : DependentCategory D}
  → (E₁' E₂' : (x : A) → DependentCategory (E x))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F₁' : DependentFunctor D₁' (E₁' x₁) F}
  → {F₂' : DependentFunctor D₂' (E₂' x₁) F}
  → {G₁' : DependentFunctor C₁' D₁' G}
  → {G₂' : DependentFunctor C₂' D₂' G}
  → {H₁' : DependentFunctor C₁' (E₁' x₂) H}
  → {H₂' : DependentFunctor C₂' (E₂' x₂) H}
  → x₂ ≡ x₁
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
  → {C₁₁' C₁₂' : DependentCategory C₁}
  → {C₂₁' C₂₂' : DependentCategory C₂}
  → {D₁₁' D₁₂' : DependentCategory D₁}
  → {D₂₁' D₂₂' : DependentCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F₁' : DependentFunctor C₁₁' C₂₁' F}
  → {F₂' : DependentFunctor C₁₂' C₂₂' F}
  → {G₁' : DependentFunctor D₁₁' D₂₁' G}
  → {G₂' : DependentFunctor D₁₂' D₂₂' G}
  → {H₁₁' : DependentFunctor C₁₁' D₁₁' H₁}
  → {H₁₂' : DependentFunctor C₁₂' D₁₂' H₁}
  → {H₂₁' : DependentFunctor C₂₁' D₂₁' H₂}
  → {H₂₂' : DependentFunctor C₂₂' D₂₂' H₂}
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F₁' G₁' H₁₁' H₂₁'
  → DependentFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → DependentFunctorSquare
    (dependent-functor-product F₁' F₂')
    (dependent-functor-product G₁' G₂')
    (dependent-functor-product H₁₁' H₁₂')
    (dependent-functor-product H₂₁' H₂₂')

dependent-functor-square-product-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁₁' C₁₂' : DependentCategory C₁}
  → {C₂₁' C₂₂' : DependentCategory C₂}
  → {D₁₁' D₁₂' : DependentCategory D₁}
  → (D₂₁' D₂₂' : (x : A) → DependentCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F₁' : DependentFunctor C₁₁' C₂₁' F}
  → {F₂' : DependentFunctor C₁₂' C₂₂' F}
  → {G₁' : DependentFunctor D₁₁' (D₂₁' x₁) G}
  → {G₂' : DependentFunctor D₁₂' (D₂₂' x₁) G}
  → {H₁₁' : DependentFunctor C₁₁' D₁₁' H₁}
  → {H₁₂' : DependentFunctor C₁₂' D₁₂' H₁}
  → {H₂₁' : DependentFunctor C₂₁' (D₂₁' x₂) H₂}
  → {H₂₂' : DependentFunctor C₂₂' (D₂₂' x₂) H₂}
  → x₂ ≡ x₁
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F₁' G₁' H₁₁' H₂₁'
  → DependentFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → DependentFunctorSquare
    (dependent-functor-product F₁' F₂')
    (dependent-functor-product G₁' G₂')
    (dependent-functor-product H₁₁' H₁₂')
    (dependent-functor-product H₂₁' H₂₂')

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

-- ### DependentFunctorIdentity

dependent-functor-identity-product {n = zero} _ p₁' p₂'
  = functor-identity-product p₁' p₂'

dependent-functor-identity-product {n = suc _}
  {C = C} {C₁' = C₁'} {C₂' = C₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-identity-product-eq
      (ChainCategory.category' C)
      (DependentCategory.category C₁')
      (DependentCategory.category C₂')
      (ChainFunctorIdentity.base p x)
      (ChainFunctorIdentity.functor' p x)
      (DependentFunctorIdentity.functor p₁' x)
      (DependentFunctorIdentity.functor p₂' x)
  }

dependent-functor-identity-product-eq _ _ _ refl
  = dependent-functor-identity-product

-- ### DependentFunctorCompose

dependent-functor-compose-product {n = zero} _ p₁' p₂'
  = functor-compose-product p₁' p₂'

dependent-functor-compose-product {n = suc _}
  {E = E} {E₁' = E₁'} {E₂' = E₂'} p p₁' p₂'
  = record
  { functor
    = λ x → dependent-functor-compose-product-eq
      (ChainCategory.category' E)
      (DependentCategory.category E₁')
      (DependentCategory.category E₂')
      (ChainFunctorCompose.base p x)
      (ChainFunctorCompose.functor' p x)
      (DependentFunctorCompose.functor p₁' x)
      (DependentFunctorCompose.functor p₂' x)
  }

dependent-functor-compose-product-eq _ _ _ refl
  = dependent-functor-compose-product

-- ### DependentFunctorSquare

dependent-functor-square-product {n = zero} _ s₁' s₂'
  = functor-square-product s₁' s₂'

dependent-functor-square-product {n = suc _}
  {D₂ = D₂} {D₂₁' = D₂₁'} {D₂₂' = D₂₂'} s s₁' s₂'
  = record
  { functor
    = λ x₁ → dependent-functor-square-product-eq
      (ChainCategory.category' D₂)
      (DependentCategory.category D₂₁')
      (DependentCategory.category D₂₂')
      (ChainFunctorSquare.base s x₁)
      (ChainFunctorSquare.functor' s x₁)
      (DependentFunctorSquare.functor s₁' x₁)
      (DependentFunctorSquare.functor s₂' x₁)
  }

dependent-functor-square-product-eq _ _ _ refl
  = dependent-functor-square-product

