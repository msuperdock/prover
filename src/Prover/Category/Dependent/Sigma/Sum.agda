module Prover.Category.Dependent.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; cons; dependent-category₀;
    dependent-category₁; dependent-functor₀; dependent-functor₁;
    dependent-functor-compose₀; dependent-functor-compose₁;
    dependent-functor-identity₀; dependent-functor-identity₁;
    dependent-functor-square₀; dependent-functor-square₁; nil)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare;
    dependent-split-functor₀; dependent-split-functor-square₀)
open import Prover.Category.Sigma.Sum
  using (category-sigma-sum; functor-compose-sigma-sum;
    functor-identity-sigma-sum; functor-sigma-sum; functor-square-sigma-sum)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-functor-snoc)
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

dependent-category-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → DependentCategory (chain-category-snoc C₂₁')
  → DependentSplitFunctor C₁₁' C₂₁'
  → DependentCategory C

-- ### DependentFunctor

dependent-functor-sigma-sum
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {D₁₁' D₂₁' : DependentCategory D}
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → {D₂₂' : DependentCategory (chain-category-snoc D₂₁')}
  → {F₁ : DependentSplitFunctor C₁₁' C₂₁'}
  → {G₁ : DependentSplitFunctor D₁₁' D₂₁'}
  → {H : ChainFunctor C D}
  → {H₁₁' : DependentFunctor C₁₁' D₁₁' H}
  → {H₂₁' : DependentFunctor C₂₁' D₂₁' H}
  → DependentFunctor C₂₂' D₂₂' (chain-functor-snoc H₂₁')
  → DependentSplitFunctorSquare H₁₁' H₂₁' F₁ G₁
  → DependentFunctor
    (dependent-category-sigma-sum C₂₂' F₁)
    (dependent-category-sigma-sum D₂₂' G₁) H

-- ### DependentFunctorIdentity

dependent-functor-identity-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → {F₁ : DependentSplitFunctor C₁₁' C₂₁'}
  → {G : ChainFunctor C C}
  → {G₁₁' : DependentFunctor C₁₁' C₁₁' G}
  → {G₂₁' : DependentFunctor C₂₁' C₂₁' G}
  → {G₂₂' : DependentFunctor C₂₂' C₂₂' (chain-functor-snoc G₂₁')}
  → (s₁ : DependentSplitFunctorSquare G₁₁' G₂₁' F₁ F₁)
  → DependentFunctorIdentity G₁₁'
  → DependentFunctorIdentity G₂₂'
  → DependentFunctorIdentity
    (dependent-functor-sigma-sum G₂₂' s₁)

dependent-functor-identity-sigma-sum-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁₁' C₂₁' : (x : A) → DependentCategory (C x))
  → (C₂₂' : (x : A) → DependentCategory (chain-category-snoc (C₂₁' x)))
  → (F₁ : (x : A) → DependentSplitFunctor (C₁₁' x) (C₂₁' x))
  → {G : ChainFunctor (C x₁) (C x₂)}
  → {G₁₁' : DependentFunctor (C₁₁' x₁) (C₁₁' x₂) G}
  → {G₂₁' : DependentFunctor (C₂₁' x₁) (C₂₁' x₂) G}
  → {G₂₂' : DependentFunctor (C₂₂' x₁) (C₂₂' x₂) (chain-functor-snoc G₂₁')}
  → (s₁ : DependentSplitFunctorSquare G₁₁' G₂₁' (F₁ x₁) (F₁ x₂))
  → x₂ ≡ x₁
  → DependentFunctorIdentity G₁₁'
  → DependentFunctorIdentity G₂₂'
  → DependentFunctorIdentity
    (dependent-functor-sigma-sum G₂₂' s₁)

-- ### DependentFunctorCompose

dependent-functor-compose-sigma-sum
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {D₁₁' D₂₁' : DependentCategory D}
  → {E₁₁' E₂₁' : DependentCategory E}
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → {D₂₂' : DependentCategory (chain-category-snoc D₂₁')}
  → {E₂₂' : DependentCategory (chain-category-snoc E₂₁')}
  → {F₁ : DependentSplitFunctor C₁₁' C₂₁'}
  → {G₁ : DependentSplitFunctor D₁₁' D₂₁'}
  → {H₁ : DependentSplitFunctor E₁₁' E₂₁'}
  → {I : ChainFunctor D E}
  → {J : ChainFunctor C D}
  → {K : ChainFunctor C E}
  → {I₁₁' : DependentFunctor D₁₁' E₁₁' I}
  → {I₂₁' : DependentFunctor D₂₁' E₂₁' I}
  → {J₁₁' : DependentFunctor C₁₁' D₁₁' J}
  → {J₂₁' : DependentFunctor C₂₁' D₂₁' J}
  → {K₁₁' : DependentFunctor C₁₁' E₁₁' K}
  → {K₂₁' : DependentFunctor C₂₁' E₂₁' K}
  → {I₂₂' : DependentFunctor D₂₂' E₂₂' (chain-functor-snoc I₂₁')}
  → {J₂₂' : DependentFunctor C₂₂' D₂₂' (chain-functor-snoc J₂₁')}
  → {K₂₂' : DependentFunctor C₂₂' E₂₂' (chain-functor-snoc K₂₁')}
  → (s₁ : DependentSplitFunctorSquare I₁₁' I₂₁' G₁ H₁)
  → (t₁ : DependentSplitFunctorSquare J₁₁' J₂₁' F₁ G₁)
  → (u₁ : DependentSplitFunctorSquare K₁₁' K₂₁' F₁ H₁)
  → DependentFunctorCompose I₁₁' J₁₁' K₁₁'
  → DependentFunctorCompose I₂₂' J₂₂' K₂₂'
  → DependentFunctorCompose
    (dependent-functor-sigma-sum I₂₂' s₁)
    (dependent-functor-sigma-sum J₂₂' t₁)
    (dependent-functor-sigma-sum K₂₂' u₁)

dependent-functor-compose-sigma-sum-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C₁₁' C₂₁' : DependentCategory C}
  → {D₁₁' D₂₁' : DependentCategory D}
  → (E₁₁' E₂₁' : (x : A) → DependentCategory (E x))
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → {D₂₂' : DependentCategory (chain-category-snoc D₂₁')}
  → (E₂₂' : (x : A) → DependentCategory (chain-category-snoc (E₂₁' x)))
  → {F₁ : DependentSplitFunctor C₁₁' C₂₁'}
  → {G₁ : DependentSplitFunctor D₁₁' D₂₁'}
  → (H₁ : (x : A) → DependentSplitFunctor (E₁₁' x) (E₂₁' x))
  → {I : ChainFunctor D (E x₁)}
  → {J : ChainFunctor C D}
  → {K : ChainFunctor C (E x₂)}
  → {I₁₁' : DependentFunctor D₁₁' (E₁₁' x₁) I}
  → {I₂₁' : DependentFunctor D₂₁' (E₂₁' x₁) I}
  → {J₁₁' : DependentFunctor C₁₁' D₁₁' J}
  → {J₂₁' : DependentFunctor C₂₁' D₂₁' J}
  → {K₁₁' : DependentFunctor C₁₁' (E₁₁' x₂) K}
  → {K₂₁' : DependentFunctor C₂₁' (E₂₁' x₂) K}
  → {I₂₂' : DependentFunctor D₂₂' (E₂₂' x₁) (chain-functor-snoc I₂₁')}
  → {J₂₂' : DependentFunctor C₂₂' D₂₂' (chain-functor-snoc J₂₁')}
  → {K₂₂' : DependentFunctor C₂₂' (E₂₂' x₂) (chain-functor-snoc K₂₁')}
  → (s₁ : DependentSplitFunctorSquare I₁₁' I₂₁' G₁ (H₁ x₁))
  → (t₁ : DependentSplitFunctorSquare J₁₁' J₂₁' F₁ G₁)
  → (u₁ : DependentSplitFunctorSquare K₁₁' K₂₁' F₁ (H₁ x₂))
  → x₂ ≡ x₁
  → DependentFunctorCompose I₁₁' J₁₁' K₁₁'
  → DependentFunctorCompose I₂₂' J₂₂' K₂₂'
  → DependentFunctorCompose
    (dependent-functor-sigma-sum I₂₂' s₁)
    (dependent-functor-sigma-sum J₂₂' t₁)
    (dependent-functor-sigma-sum K₂₂' u₁)

-- ### DependentFunctorSquare

dependent-functor-square-sigma-sum
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁₁₁' C₁₂₁' : DependentCategory C₁}
  → {C₂₁₁' C₂₂₁' : DependentCategory C₂}
  → {D₁₁₁' D₁₂₁' : DependentCategory D₁}
  → {D₂₁₁' D₂₂₁' : DependentCategory D₂}
  → {C₁₂₂' : DependentCategory (chain-category-snoc C₁₂₁')}
  → {C₂₂₂' : DependentCategory (chain-category-snoc C₂₂₁')}
  → {D₁₂₂' : DependentCategory (chain-category-snoc D₁₂₁')}
  → {D₂₂₂' : DependentCategory (chain-category-snoc D₂₂₁')}
  → {F₁₁ : DependentSplitFunctor C₁₁₁' C₁₂₁'}
  → {F₂₁ : DependentSplitFunctor C₂₁₁' C₂₂₁'}
  → {G₁₁ : DependentSplitFunctor D₁₁₁' D₁₂₁'}
  → {G₂₁ : DependentSplitFunctor D₂₁₁' D₂₂₁'}
  → {H : ChainFunctor C₁ C₂}
  → {I : ChainFunctor D₁ D₂}
  → {J₁ : ChainFunctor C₁ D₁}
  → {J₂ : ChainFunctor C₂ D₂}
  → {H₁₁' : DependentFunctor C₁₁₁' C₂₁₁' H}
  → {H₂₁' : DependentFunctor C₁₂₁' C₂₂₁' H}
  → {I₁₁' : DependentFunctor D₁₁₁' D₂₁₁' I}
  → {I₂₁' : DependentFunctor D₁₂₁' D₂₂₁' I}
  → {J₁₁₁' : DependentFunctor C₁₁₁' D₁₁₁' J₁}
  → {J₁₂₁' : DependentFunctor C₁₂₁' D₁₂₁' J₁}
  → {J₂₁₁' : DependentFunctor C₂₁₁' D₂₁₁' J₂}
  → {J₂₂₁' : DependentFunctor C₂₂₁' D₂₂₁' J₂}
  → {H₂₂' : DependentFunctor C₁₂₂' C₂₂₂' (chain-functor-snoc H₂₁')}
  → {I₂₂' : DependentFunctor D₁₂₂' D₂₂₂' (chain-functor-snoc I₂₁')}
  → {J₁₂₂' : DependentFunctor C₁₂₂' D₁₂₂' (chain-functor-snoc J₁₂₁')}
  → {J₂₂₂' : DependentFunctor C₂₂₂' D₂₂₂' (chain-functor-snoc J₂₂₁')}
  → (s₁ : DependentSplitFunctorSquare H₁₁' H₂₁' F₁₁ F₂₁)
  → (t₁ : DependentSplitFunctorSquare I₁₁' I₂₁' G₁₁ G₂₁)
  → (u₁₁ : DependentSplitFunctorSquare J₁₁₁' J₁₂₁' F₁₁ G₁₁)
  → (u₂₁ : DependentSplitFunctorSquare J₂₁₁' J₂₂₁' F₂₁ G₂₁)
  → DependentFunctorSquare H₁₁' I₁₁' J₁₁₁' J₂₁₁'
  → DependentFunctorSquare H₂₂' I₂₂' J₁₂₂' J₂₂₂'
  → DependentFunctorSquare
    (dependent-functor-sigma-sum H₂₂' s₁)
    (dependent-functor-sigma-sum I₂₂' t₁)
    (dependent-functor-sigma-sum J₁₂₂' u₁₁)
    (dependent-functor-sigma-sum J₂₂₂' u₂₁)

dependent-functor-square-sigma-sum-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁₁₁' C₁₂₁' : DependentCategory C₁}
  → {C₂₁₁' C₂₂₁' : DependentCategory C₂}
  → {D₁₁₁' D₁₂₁' : DependentCategory D₁}
  → (D₂₁₁' D₂₂₁' : (x : A) → DependentCategory (D₂ x))
  → {C₁₂₂' : DependentCategory (chain-category-snoc C₁₂₁')}
  → {C₂₂₂' : DependentCategory (chain-category-snoc C₂₂₁')}
  → {D₁₂₂' : DependentCategory (chain-category-snoc D₁₂₁')}
  → (D₂₂₂' : (x : A) → DependentCategory (chain-category-snoc (D₂₂₁' x)))
  → {F₁₁ : DependentSplitFunctor C₁₁₁' C₁₂₁'}
  → {F₂₁ : DependentSplitFunctor C₂₁₁' C₂₂₁'}
  → {G₁₁ : DependentSplitFunctor D₁₁₁' D₁₂₁'}
  → (G₂₁ : (x : A) → DependentSplitFunctor (D₂₁₁' x) (D₂₂₁' x))
  → {H : ChainFunctor C₁ C₂}
  → {I : ChainFunctor D₁ (D₂ x₁)}
  → {J₁ : ChainFunctor C₁ D₁}
  → {J₂ : ChainFunctor C₂ (D₂ x₂)}
  → {H₁₁' : DependentFunctor C₁₁₁' C₂₁₁' H}
  → {H₂₁' : DependentFunctor C₁₂₁' C₂₂₁' H}
  → {I₁₁' : DependentFunctor D₁₁₁' (D₂₁₁' x₁) I}
  → {I₂₁' : DependentFunctor D₁₂₁' (D₂₂₁' x₁) I}
  → {J₁₁₁' : DependentFunctor C₁₁₁' D₁₁₁' J₁}
  → {J₁₂₁' : DependentFunctor C₁₂₁' D₁₂₁' J₁}
  → {J₂₁₁' : DependentFunctor C₂₁₁' (D₂₁₁' x₂) J₂}
  → {J₂₂₁' : DependentFunctor C₂₂₁' (D₂₂₁' x₂) J₂}
  → {H₂₂' : DependentFunctor C₁₂₂' C₂₂₂' (chain-functor-snoc H₂₁')}
  → {I₂₂' : DependentFunctor D₁₂₂' (D₂₂₂' x₁) (chain-functor-snoc I₂₁')}
  → {J₁₂₂' : DependentFunctor C₁₂₂' D₁₂₂' (chain-functor-snoc J₁₂₁')}
  → {J₂₂₂' : DependentFunctor C₂₂₂' (D₂₂₂' x₂) (chain-functor-snoc J₂₂₁')}
  → (s₁ : DependentSplitFunctorSquare H₁₁' H₂₁' F₁₁ F₂₁)
  → (t₁ : DependentSplitFunctorSquare I₁₁' I₂₁' G₁₁ (G₂₁ x₁))
  → (u₁₁ : DependentSplitFunctorSquare J₁₁₁' J₁₂₁' F₁₁ G₁₁)
  → (u₂₁ : DependentSplitFunctorSquare J₂₁₁' J₂₂₁' F₂₁ (G₂₁ x₂))
  → x₂ ≡ x₁
  → DependentFunctorSquare H₁₁' I₁₁' J₁₁₁' J₂₁₁'
  → DependentFunctorSquare H₂₂' I₂₂' J₁₂₂' J₂₂₂'
  → DependentFunctorSquare
    (dependent-functor-sigma-sum H₂₂' s₁)
    (dependent-functor-sigma-sum I₂₂' t₁)
    (dependent-functor-sigma-sum J₁₂₂' u₁₁)
    (dependent-functor-sigma-sum J₂₂₂' u₂₁)

-- ## Definitions

-- ### DependentCategory

dependent-category-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  C₂₂' F₁
  = nil
    (category-sigma-sum
      {C₁₁ = dependent-category₀ C₁₁'}
      {C₂₁ = dependent-category₀ C₂₁'}
      (dependent-category₁ C₂₂')
      (dependent-split-functor₀ F₁))
dependent-category-sigma-sum
  {n = suc _}
  {C = C}
  {C₁₁' = C₁₁'}
  C₂₂' F₁
  = cons
    (λ x → dependent-category-sigma-sum
      (DependentCategory.tail C₂₂' x)
      (DependentSplitFunctor.tail F₁ x))
    (λ f → dependent-functor-sigma-sum
      (DependentCategory.dependent-functor C₂₂' f)
      (DependentSplitFunctor.dependent-split-functor-square F₁ f))
    (λ x → dependent-functor-identity-sigma-sum
      (DependentSplitFunctor.dependent-split-functor-square F₁
        (ChainCategory.identity C x))
      (DependentCategory.dependent-functor-identity C₁₁' x)
      (DependentCategory.dependent-functor-identity C₂₂' x))
    (λ f g → dependent-functor-compose-sigma-sum
      (DependentSplitFunctor.dependent-split-functor-square F₁ f)
      (DependentSplitFunctor.dependent-split-functor-square F₁ g)
      (DependentSplitFunctor.dependent-split-functor-square F₁
        (ChainCategory.compose C f g))
      (DependentCategory.dependent-functor-compose C₁₁' f g)
      (DependentCategory.dependent-functor-compose C₂₂' f g))

-- ### DependentFunctor

dependent-functor-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {D₁₁' = D₁₁'} {D₂₁' = D₂₁'}
  {C₂₂' = C₂₂'} {D₂₂' = D₂₂'}
  {F₁ = F₁} {G₁ = G₁}
  {H₁₁' = H₁₁'}
  H₂₂' s₁
  = nil
    (functor-sigma-sum
      {C₁₁ = dependent-category₀ C₁₁'}
      {C₂₁ = dependent-category₀ C₂₁'}
      {D₁₁ = dependent-category₀ D₁₁'}
      {D₂₁ = dependent-category₀ D₂₁'}
      {C₂₂ = dependent-category₁ C₂₂'}
      {D₂₂ = dependent-category₁ D₂₂'}
      {F₁ = dependent-split-functor₀ F₁}
      {G₁ = dependent-split-functor₀ G₁}
      {H₁₁ = dependent-functor₀ H₁₁'}
      (dependent-functor₁ H₂₂')
      (dependent-split-functor-square₀ s₁))
dependent-functor-sigma-sum
  {n = suc _}
  {F₁ = F₁} {G₁ = G₁} {H = H}
  {H₁₁' = H₁₁'}
  H₂₂' s₁
  = cons
    (λ x → dependent-functor-sigma-sum
      (DependentFunctor.tail H₂₂' x)
      (DependentSplitFunctorSquare.tail s₁ x))
    (λ {x = x} {y = y} f → dependent-functor-square-sigma-sum
      (DependentSplitFunctor.dependent-split-functor-square F₁ f)
      (DependentSplitFunctor.dependent-split-functor-square G₁
        (ChainFunctor.map H f))
      (DependentSplitFunctorSquare.tail s₁ x)
      (DependentSplitFunctorSquare.tail s₁ y)
      (DependentFunctor.dependent-functor-square H₁₁' f)
      (DependentFunctor.dependent-functor-square H₂₂' f))

-- ### DependentFunctorIdentity

dependent-functor-identity-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {C₂₂' = C₂₂'}
  {F₁ = F₁}
  {G₁₁' = G₁₁'}
  {G₂₂' = G₂₂'}
  s₁ p₁₁ p₂₂
  = nil
    (functor-identity-sigma-sum
      {C₁₁ = dependent-category₀ C₁₁'}
      {C₂₁ = dependent-category₀ C₂₁'}
      {C₂₂ = dependent-category₁ C₂₂'}
      {F₁ = dependent-split-functor₀ F₁}
      {G₁₁ = dependent-functor₀ G₁₁'}
      {G₂₂ = dependent-functor₁ G₂₂'}
      (dependent-split-functor-square₀ s₁)
      (dependent-functor-identity₀ p₁₁)
      (dependent-functor-identity₁ p₂₂))
dependent-functor-identity-sigma-sum
  {n = suc _}
  {C = C}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {C₂₂' = C₂₂'}
  {F₁ = F₁}
  s₁ p₁₁ p₂₂
  = cons
    (DependentFunctorIdentity.head p₁₁)
    (λ x → dependent-functor-identity-sigma-sum-eq
      (ChainCategory.tail C)
      (DependentCategory.tail C₁₁')
      (DependentCategory.tail C₂₁')
      (DependentCategory.tail C₂₂')
      (DependentSplitFunctor.tail F₁)
      (DependentSplitFunctorSquare.tail s₁ x)
      (DependentFunctorIdentity.base p₁₁ x)
      (DependentFunctorIdentity.tail p₁₁ x)
      (DependentFunctorIdentity.tail p₂₂ x))

dependent-functor-identity-sigma-sum-eq _ _ _ _ _ s₁ refl
  = dependent-functor-identity-sigma-sum s₁

-- ### DependentFunctorCompose

dependent-functor-compose-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {D₁₁' = D₁₁'} {D₂₁' = D₂₁'}
  {E₁₁' = E₁₁'} {E₂₁' = E₂₁'} 
  {C₂₂' = C₂₂'} {D₂₂' = D₂₂'} {E₂₂' = E₂₂'}
  {F₁ = F₁} {G₁ = G₁} {H₁ = H₁}
  {I₁₁' = I₁₁'} {J₁₁' = J₁₁'} {K₁₁' = K₁₁'}
  {I₂₂' = I₂₂'} {J₂₂' = J₂₂'} {K₂₂' = K₂₂'}
  s₁ t₁ u₁ p₁₁ p₂₂
  = nil
    (functor-compose-sigma-sum
      {C₁₁ = dependent-category₀ C₁₁'}
      {C₂₁ = dependent-category₀ C₂₁'}
      {D₁₁ = dependent-category₀ D₁₁'}
      {D₂₁ = dependent-category₀ D₂₁'}
      {E₁₁ = dependent-category₀ E₁₁'}
      {E₂₁ = dependent-category₀ E₂₁'}
      {C₂₂ = dependent-category₁ C₂₂'}
      {D₂₂ = dependent-category₁ D₂₂'}
      {E₂₂ = dependent-category₁ E₂₂'}
      {I₁ = dependent-split-functor₀ F₁}
      {J₁ = dependent-split-functor₀ G₁}
      {K₁ = dependent-split-functor₀ H₁}
      {L₁₁ = dependent-functor₀ I₁₁'}
      {M₁₁ = dependent-functor₀ J₁₁'}
      {N₁₁ = dependent-functor₀ K₁₁'}
      {L₂₂ = dependent-functor₁ I₂₂'}
      {M₂₂ = dependent-functor₁ J₂₂'}
      {N₂₂ = dependent-functor₁ K₂₂'}
      (dependent-split-functor-square₀ s₁)
      (dependent-split-functor-square₀ t₁)
      (dependent-split-functor-square₀ u₁)
      (dependent-functor-compose₀ p₁₁)
      (dependent-functor-compose₁ p₂₂))
dependent-functor-compose-sigma-sum
  {n = suc _}
  {E = E}
  {E₁₁' = E₁₁'} {E₂₁' = E₂₁'}
  {E₂₂' = E₂₂'}
  {H₁ = H₁}
  {J = J}
  s₁ t₁ u₁ p₁₁ p₂₂
  = cons
    (DependentFunctorCompose.head p₁₁)
    (λ x → dependent-functor-compose-sigma-sum-eq
      (ChainCategory.tail E)
      (DependentCategory.tail E₁₁')
      (DependentCategory.tail E₂₁')
      (DependentCategory.tail E₂₂')
      (DependentSplitFunctor.tail H₁)
      (DependentSplitFunctorSquare.tail s₁ (ChainFunctor.base J x))
      (DependentSplitFunctorSquare.tail t₁ x)
      (DependentSplitFunctorSquare.tail u₁ x)
      (DependentFunctorCompose.base p₁₁ x)
      (DependentFunctorCompose.tail p₁₁ x)
      (DependentFunctorCompose.tail p₂₂ x))

dependent-functor-compose-sigma-sum-eq _ _ _ _ _ s₁ t₁ u₁ refl
  = dependent-functor-compose-sigma-sum s₁ t₁ u₁

-- ### DependentFunctorSquare

dependent-functor-square-sigma-sum
  {n = zero}
  {C₁₁₁' = C₁₁₁'} {C₁₂₁' = C₁₂₁'}
  {C₂₁₁' = C₂₁₁'} {C₂₂₁' = C₂₂₁'}
  {D₁₁₁' = D₁₁₁'} {D₁₂₁' = D₁₂₁'}
  {D₂₁₁' = D₂₁₁'} {D₂₂₁' = D₂₂₁'}
  {C₁₂₂' = C₁₂₂'} {C₂₂₂' = C₂₂₂'} {D₁₂₂' = D₁₂₂'} {D₂₂₂' = D₂₂₂'}
  {F₁₁ = F₁₁} {F₂₁ = F₂₁} {G₁₁ = G₁₁} {G₂₁ = G₂₁}
  {H₁₁' = H₁₁'} {I₁₁' = I₁₁'} {J₁₁₁' = J₁₁₁'} {J₂₁₁' = J₂₁₁'}
  {H₂₂' = H₂₂'} {I₂₂' = I₂₂'} {J₁₂₂' = J₁₂₂'} {J₂₂₂' = J₂₂₂'}
  s₁ t₁ u₁₁ u₂₁ s₁₁ s₂₂
  = nil
    (functor-square-sigma-sum
      {C₁₁₁ = dependent-category₀ C₁₁₁'}
      {C₁₂₁ = dependent-category₀ C₁₂₁'}
      {C₂₁₁ = dependent-category₀ C₂₁₁'}
      {C₂₂₁ = dependent-category₀ C₂₂₁'}
      {D₁₁₁ = dependent-category₀ D₁₁₁'}
      {D₁₂₁ = dependent-category₀ D₁₂₁'}
      {D₂₁₁ = dependent-category₀ D₂₁₁'}
      {D₂₂₁ = dependent-category₀ D₂₂₁'}
      {C₁₂₂ = dependent-category₁ C₁₂₂'}
      {C₂₂₂ = dependent-category₁ C₂₂₂'}
      {D₁₂₂ = dependent-category₁ D₁₂₂'}
      {D₂₂₂ = dependent-category₁ D₂₂₂'}
      {F₁₁ = dependent-split-functor₀ F₁₁}
      {F₂₁ = dependent-split-functor₀ F₂₁}
      {G₁₁ = dependent-split-functor₀ G₁₁}
      {G₂₁ = dependent-split-functor₀ G₂₁}
      {H₁₁ = dependent-functor₀ H₁₁'}
      {I₁₁ = dependent-functor₀ I₁₁'}
      {J₁₁₁ = dependent-functor₀ J₁₁₁'}
      {J₂₁₁ = dependent-functor₀ J₂₁₁'}
      {H₂₂ = dependent-functor₁ H₂₂'}
      {I₂₂ = dependent-functor₁ I₂₂'}
      {J₁₂₂ = dependent-functor₁ J₁₂₂'}
      {J₂₂₂ = dependent-functor₁ J₂₂₂'}
      (dependent-split-functor-square₀ s₁)
      (dependent-split-functor-square₀ t₁)
      (dependent-split-functor-square₀ u₁₁)
      (dependent-split-functor-square₀ u₂₁)
      (dependent-functor-square₀ s₁₁)
      (dependent-functor-square₁ s₂₂))
dependent-functor-square-sigma-sum
  {n = suc _}
  {D₂ = D₂}
  {D₂₁₁' = D₂₁₁'} {D₂₂₁' = D₂₂₁'}
  {D₂₂₂' = D₂₂₂'}
  {G₂₁ = G₂₁}
  {H = H} {J₁ = J₁}
  s₁ t₁ u₁₁ u₂₁ v₁₁ v₂₂
  = cons
    (DependentFunctorSquare.head v₁₁)
    (λ x₁ → dependent-functor-square-sigma-sum-eq
      (ChainCategory.tail D₂)
      (DependentCategory.tail D₂₁₁')
      (DependentCategory.tail D₂₂₁')
      (DependentCategory.tail D₂₂₂')
      (DependentSplitFunctor.tail G₂₁)
      (DependentSplitFunctorSquare.tail s₁ x₁)
      (DependentSplitFunctorSquare.tail t₁ (ChainFunctor.base J₁ x₁))
      (DependentSplitFunctorSquare.tail u₁₁ x₁)
      (DependentSplitFunctorSquare.tail u₂₁ (ChainFunctor.base H x₁))
      (DependentFunctorSquare.base v₁₁ x₁)
      (DependentFunctorSquare.tail v₁₁ x₁)
      (DependentFunctorSquare.tail v₂₂ x₁))

dependent-functor-square-sigma-sum-eq _ _ _ _ _ s₁ t₁ u₁₁ u₂₁ refl
  = dependent-functor-square-sigma-sum s₁ t₁ u₁₁ u₂₁
