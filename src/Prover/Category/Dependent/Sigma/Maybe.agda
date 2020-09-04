module Prover.Category.Dependent.Sigma.Maybe where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; cons; dependent-category₀;
    dependent-category₁; dependent-functor₁; dependent-functor-compose₁;
    dependent-functor-identity₁; dependent-functor-square₁; nil)
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
  → DependentCategory
    (chain-category-snoc C₁')
  → DependentCategory C

-- ### DependentFunctor

dependent-functor-sigma-maybe
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {D₁' : DependentCategory D}
  → {C₂' : DependentCategory
    (chain-category-snoc C₁')}
  → {D₂' : DependentCategory
    (chain-category-snoc D₁')}
  → {F : ChainFunctor C D}
  → (F₁' : DependentFunctor C₁' D₁' F)
  → DependentFunctor C₂' D₂'
    (chain-functor-snoc F₁')
  → DependentFunctor
    (dependent-category-sigma-maybe C₁' C₂')
    (dependent-category-sigma-maybe D₁' D₂') F

-- ### DependentFunctorIdentity

dependent-functor-identity-sigma-maybe
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentCategory
    (chain-category-snoc C₁')}
  → {F : ChainFunctor C C}
  → (F₁' : DependentFunctor C₁' C₁' F)
  → {F₂' : DependentFunctor C₂' C₂'
    (chain-functor-snoc F₁')}
  → DependentFunctorIdentity F₂'
  → DependentFunctorIdentity
    (dependent-functor-sigma-maybe F₁' F₂')

dependent-functor-identity-sigma-maybe-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁' : (x : A) → DependentCategory (C x))
  → (C₂' : (x : A) → DependentCategory
    (chain-category-snoc (C₁' x)))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → (F₁' : DependentFunctor (C₁' x₁) (C₁' x₂) F)
  → {F₂' : DependentFunctor (C₂' x₁) (C₂' x₂)
    (chain-functor-snoc F₁')}
  → x₂ ≡ x₁
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
  → {C₂' : DependentCategory
    (chain-category-snoc C₁')}
  → {D₂' : DependentCategory
    (chain-category-snoc D₁')}
  → {E₂' : DependentCategory
    (chain-category-snoc E₁')}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → (F₁' : DependentFunctor D₁' E₁' F)
  → (G₁' : DependentFunctor C₁' D₁' G)
  → (H₁' : DependentFunctor C₁' E₁' H)
  → {F₂' : DependentFunctor D₂' E₂'
    (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor C₂' D₂'
    (chain-functor-snoc G₁')}
  → {H₂' : DependentFunctor C₂' E₂'
    (chain-functor-snoc H₁')}
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
  → (F₁' : DependentFunctor D₁' (E₁' x₁) F)
  → (G₁' : DependentFunctor C₁' D₁' G)
  → (H₁' : DependentFunctor C₁' (E₁' x₂) H)
  → {F₂' : DependentFunctor D₂' (E₂' x₁) (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor C₂' D₂' (chain-functor-snoc G₁')}
  → {H₂' : DependentFunctor C₂' (E₂' x₂) (chain-functor-snoc H₁')}
  → x₂ ≡ x₁
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
  → {C₁₂' : DependentCategory
    (chain-category-snoc C₁₁')}
  → {C₂₂' : DependentCategory
    (chain-category-snoc C₂₁')}
  → {D₁₂' : DependentCategory
    (chain-category-snoc D₁₁')}
  → {D₂₂' : DependentCategory
    (chain-category-snoc D₂₁')}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → (F₁' : DependentFunctor C₁₁' C₂₁' F)
  → (G₁' : DependentFunctor D₁₁' D₂₁' G)
  → (H₁₁' : DependentFunctor C₁₁' D₁₁' H₁)
  → (H₂₁' : DependentFunctor C₂₁' D₂₁' H₂)
  → {F₂' : DependentFunctor C₁₂' C₂₂'
    (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor D₁₂' D₂₂'
    (chain-functor-snoc G₁')}
  → {H₁₂' : DependentFunctor C₁₂' D₁₂'
    (chain-functor-snoc H₁₁')}
  → {H₂₂' : DependentFunctor C₂₂' D₂₂'
    (chain-functor-snoc H₂₁')}
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
  → (F₁' : DependentFunctor C₁₁' C₂₁' F)
  → (G₁' : DependentFunctor D₁₁' (D₂₁' x₁) G)
  → (H₁₁' : DependentFunctor C₁₁' D₁₁' H₁)
  → (H₂₁' : DependentFunctor C₂₁' (D₂₁' x₂) H₂)
  → {F₂' : DependentFunctor C₁₂' C₂₂' (chain-functor-snoc F₁')}
  → {G₂' : DependentFunctor D₁₂' (D₂₂' x₁) (chain-functor-snoc G₁')}
  → {H₁₂' : DependentFunctor C₁₂' D₁₂' (chain-functor-snoc H₁₁')}
  → {H₂₂' : DependentFunctor C₂₂' (D₂₂' x₂) (chain-functor-snoc H₂₁')}
  → x₂ ≡ x₁
  → DependentFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → DependentFunctorSquare
    (dependent-functor-sigma-maybe F₁' F₂')
    (dependent-functor-sigma-maybe G₁' G₂')
    (dependent-functor-sigma-maybe H₁₁' H₁₂')
    (dependent-functor-sigma-maybe H₂₁' H₂₂')

-- ## Definitions

-- ### DependentCategory

dependent-category-sigma-maybe
  {n = zero} C₁' C₂'
  = nil
    (category-sigma-maybe
      {C₁ = dependent-category₀ C₁'}
      (dependent-category₁ C₂'))
dependent-category-sigma-maybe
  {n = suc _}
  {C = C} C₁' C₂'
  = cons
    (λ x → dependent-category-sigma-maybe
      (DependentCategory.tail C₁' x)
      (DependentCategory.tail C₂' x))
    (λ f → dependent-functor-sigma-maybe
      (DependentCategory.dependent-functor C₁' f)
      (DependentCategory.dependent-functor C₂' f))
    (λ x → dependent-functor-identity-sigma-maybe
      (DependentCategory.dependent-functor C₁' (ChainCategory.identity C x))
      (DependentCategory.dependent-functor-identity C₂' x))
    (λ f g → dependent-functor-compose-sigma-maybe
      (DependentCategory.dependent-functor C₁' f)
      (DependentCategory.dependent-functor C₁' g)
      (DependentCategory.dependent-functor C₁' (ChainCategory.compose C f g))
      (DependentCategory.dependent-functor-compose C₂' f g))

-- ### DependentFunctor

dependent-functor-sigma-maybe
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'}
  {C₂' = C₂'} {D₂' = D₂'} _ F₂'
  = nil
    (functor-sigma-maybe
      {C₁ = dependent-category₀ C₁'}
      {D₁ = dependent-category₀ D₁'}
      {C₂ = dependent-category₁ C₂'}
      {D₂ = dependent-category₁ D₂'}
      (dependent-functor₁ F₂'))
dependent-functor-sigma-maybe
  {n = suc _}
  {C₁' = C₁'} {D₁' = D₁'}
  {F = F} F₁' F₂'
  = cons
    (λ x → dependent-functor-sigma-maybe
      (DependentFunctor.tail F₁' x)
      (DependentFunctor.tail F₂' x))
    (λ {x = x} {y = y} f → dependent-functor-square-sigma-maybe
      (DependentCategory.dependent-functor C₁' f)
      (DependentCategory.dependent-functor D₁' (ChainFunctor.map F f))
      (DependentFunctor.tail F₁' x)
      (DependentFunctor.tail F₁' y)
      (DependentFunctor.dependent-functor-square F₂' f))

-- ### DependentFunctorIdentity

dependent-functor-identity-sigma-maybe
  {n = zero}
  {C₁' = C₁'}
  {C₂' = C₂'} _
  {F₂' = F₂'} p₂
  = nil
    (functor-identity-sigma-maybe
      {C₁ = dependent-category₀ C₁'}
      {C₂ = dependent-category₁ C₂'}
      {F₂ = dependent-functor₁ F₂'}
      (dependent-functor-identity₁ p₂))
dependent-functor-identity-sigma-maybe
  {n = suc _}
  {C = C}
  {C₁' = C₁'}
  {C₂' = C₂'} F₁' p₂
  = cons
    (DependentFunctorIdentity.head p₂)
    (λ x → dependent-functor-identity-sigma-maybe-eq
      (ChainCategory.tail C)
      (DependentCategory.tail C₁')
      (DependentCategory.tail C₂')
      (DependentFunctor.tail F₁' x)
      (DependentFunctorIdentity.base p₂ x)
      (DependentFunctorIdentity.tail p₂ x))

dependent-functor-identity-sigma-maybe-eq _ _ _ F₁' refl
  = dependent-functor-identity-sigma-maybe F₁'

-- ### DependentFunctorCompose

dependent-functor-compose-sigma-maybe
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'} {E₁' = E₁'}
  {C₂' = C₂'} {D₂' = D₂'} {E₂' = E₂'} _ _ _
  {F₂' = F₂'} {G₂' = G₂'} {H₂' = H₂'} p₂
  = nil
    (functor-compose-sigma-maybe
      {C₁ = dependent-category₀ C₁'}
      {D₁ = dependent-category₀ D₁'}
      {E₁ = dependent-category₀ E₁'}
      {C₂ = dependent-category₁ C₂'}
      {D₂ = dependent-category₁ D₂'}
      {E₂ = dependent-category₁ E₂'}
      {F₂ = dependent-functor₁ F₂'}
      {G₂ = dependent-functor₁ G₂'}
      {H₂ = dependent-functor₁ H₂'}
      (dependent-functor-compose₁ p₂))
dependent-functor-compose-sigma-maybe
  {n = suc _}
  {E = E}
  {E₁' = E₁'}
  {E₂' = E₂'}
  {G = G} F₁' G₁' H₁' p₂
  = cons
    (DependentFunctorCompose.head p₂)
    (λ x → dependent-functor-compose-sigma-maybe-eq
      (ChainCategory.tail E)
      (DependentCategory.tail E₁')
      (DependentCategory.tail E₂')
      (DependentFunctor.tail F₁' (ChainFunctor.base G x))
      (DependentFunctor.tail G₁' x)
      (DependentFunctor.tail H₁' x)
      (DependentFunctorCompose.base p₂ x)
      (DependentFunctorCompose.tail p₂ x))

dependent-functor-compose-sigma-maybe-eq _ _ _ F₁' G₁' H₁' refl
  = dependent-functor-compose-sigma-maybe F₁' G₁' H₁'

-- ### DependentFunctorSquare

dependent-functor-square-sigma-maybe
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'} {D₁₁' = D₁₁'} {D₂₁' = D₂₁'}
  {C₁₂' = C₁₂'} {C₂₂' = C₂₂'} {D₁₂' = D₁₂'} {D₂₂' = D₂₂'} _ _ _ _
  {F₂' = F₂'} {G₂' = G₂'} {H₁₂' = H₁₂'} {H₂₂' = H₂₂'} s₂
  = nil
    (functor-square-sigma-maybe
      {C₁₁ = dependent-category₀ C₁₁'}
      {C₂₁ = dependent-category₀ C₂₁'}
      {D₁₁ = dependent-category₀ D₁₁'}
      {D₂₁ = dependent-category₀ D₂₁'}
      {C₁₂ = dependent-category₁ C₁₂'}
      {C₂₂ = dependent-category₁ C₂₂'}
      {D₁₂ = dependent-category₁ D₁₂'}
      {D₂₂ = dependent-category₁ D₂₂'}
      {F₂ = dependent-functor₁ F₂'}
      {G₂ = dependent-functor₁ G₂'}
      {H₁₂ = dependent-functor₁ H₁₂'}
      {H₂₂ = dependent-functor₁ H₂₂'}
      (dependent-functor-square₁ s₂))
dependent-functor-square-sigma-maybe
  {n = suc _}
  {D₂ = D₂}
  {D₂₁' = D₂₁'} {D₂₂' = D₂₂'}
  {F = F} {H₁ = H₁} F₁' G₁' H₁₁' H₂₁' s₂
  = cons
    (DependentFunctorSquare.head s₂)
    (λ x₁ → dependent-functor-square-sigma-maybe-eq
      (ChainCategory.tail D₂)
      (DependentCategory.tail D₂₁')
      (DependentCategory.tail D₂₂')
      (DependentFunctor.tail F₁' x₁)
      (DependentFunctor.tail G₁' (ChainFunctor.base H₁ x₁))
      (DependentFunctor.tail H₁₁' x₁)
      (DependentFunctor.tail H₂₁' (ChainFunctor.base F x₁))
      (DependentFunctorSquare.base s₂ x₁)
      (DependentFunctorSquare.tail s₂ x₁))

dependent-functor-square-sigma-maybe-eq _ _ _ F₁' G₁' H₁₁' H₂₁' refl
  = dependent-functor-square-sigma-maybe F₁' G₁' H₁₁' H₂₁'

