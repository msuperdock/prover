module Prover.Category.Indexed.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; cons; indexed-category₀;
    indexed-category₁; indexed-functor₀; indexed-functor₁;
    indexed-functor-compose₀; indexed-functor-compose₁;
    indexed-functor-identity₀; indexed-functor-identity₁;
    indexed-functor-square₀; indexed-functor-square₁; nil)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor; IndexedSplitFunctorSquare; indexed-split-functor₀;
    indexed-split-functor-square₀)
open import Prover.Category.Sigma.Sum
  using (category-sigma-sum; functor-compose-sigma-sum;
    functor-identity-sigma-sum; functor-sigma-sum; functor-square-sigma-sum)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-functor-snoc)
open import Prover.Prelude


-- ## Types

-- ### IndexedCategory

indexed-category-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : IndexedCategory C}
  → IndexedCategory (chain-category-snoc C₂₁')
  → IndexedSplitFunctor C₁₁' C₂₁'
  → IndexedCategory C

-- ### IndexedFunctor

indexed-functor-sigma-sum
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {D₁₁' D₂₁' : IndexedCategory D}
  → {C₂₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → {D₂₂' : IndexedCategory (chain-category-snoc D₂₁')}
  → {F₁ : IndexedSplitFunctor C₁₁' C₂₁'}
  → {G₁ : IndexedSplitFunctor D₁₁' D₂₁'}
  → {H : ChainFunctor C D}
  → {H₁₁' : IndexedFunctor C₁₁' D₁₁' H}
  → {H₂₁' : IndexedFunctor C₂₁' D₂₁' H}
  → IndexedFunctor C₂₂' D₂₂' (chain-functor-snoc H₂₁')
  → IndexedSplitFunctorSquare H₁₁' H₂₁' F₁ G₁
  → IndexedFunctor
    (indexed-category-sigma-sum C₂₂' F₁)
    (indexed-category-sigma-sum D₂₂' G₁) H

-- ### IndexedFunctorIdentity

indexed-functor-identity-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {C₂₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → {F₁ : IndexedSplitFunctor C₁₁' C₂₁'}
  → {G : ChainFunctor C C}
  → {G₁₁' : IndexedFunctor C₁₁' C₁₁' G}
  → {G₂₁' : IndexedFunctor C₂₁' C₂₁' G}
  → {G₂₂' : IndexedFunctor C₂₂' C₂₂' (chain-functor-snoc G₂₁')}
  → (s₁ : IndexedSplitFunctorSquare G₁₁' G₂₁' F₁ F₁)
  → IndexedFunctorIdentity G₁₁'
  → IndexedFunctorIdentity G₂₂'
  → IndexedFunctorIdentity
    (indexed-functor-sigma-sum G₂₂' s₁)

indexed-functor-identity-sigma-sum-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁₁' C₂₁' : (x : A) → IndexedCategory (C x))
  → (C₂₂' : (x : A) → IndexedCategory (chain-category-snoc (C₂₁' x)))
  → (F₁ : (x : A) → IndexedSplitFunctor (C₁₁' x) (C₂₁' x))
  → {G : ChainFunctor (C x₁) (C x₂)}
  → {G₁₁' : IndexedFunctor (C₁₁' x₁) (C₁₁' x₂) G}
  → {G₂₁' : IndexedFunctor (C₂₁' x₁) (C₂₁' x₂) G}
  → {G₂₂' : IndexedFunctor (C₂₂' x₁) (C₂₂' x₂) (chain-functor-snoc G₂₁')}
  → (s₁ : IndexedSplitFunctorSquare G₁₁' G₂₁' (F₁ x₁) (F₁ x₂))
  → x₂ ≡ x₁
  → IndexedFunctorIdentity G₁₁'
  → IndexedFunctorIdentity G₂₂'
  → IndexedFunctorIdentity
    (indexed-functor-sigma-sum G₂₂' s₁)

-- ### IndexedFunctorCompose

indexed-functor-compose-sigma-sum
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {D₁₁' D₂₁' : IndexedCategory D}
  → {E₁₁' E₂₁' : IndexedCategory E}
  → {C₂₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → {D₂₂' : IndexedCategory (chain-category-snoc D₂₁')}
  → {E₂₂' : IndexedCategory (chain-category-snoc E₂₁')}
  → {F₁ : IndexedSplitFunctor C₁₁' C₂₁'}
  → {G₁ : IndexedSplitFunctor D₁₁' D₂₁'}
  → {H₁ : IndexedSplitFunctor E₁₁' E₂₁'}
  → {I : ChainFunctor D E}
  → {J : ChainFunctor C D}
  → {K : ChainFunctor C E}
  → {I₁₁' : IndexedFunctor D₁₁' E₁₁' I}
  → {I₂₁' : IndexedFunctor D₂₁' E₂₁' I}
  → {J₁₁' : IndexedFunctor C₁₁' D₁₁' J}
  → {J₂₁' : IndexedFunctor C₂₁' D₂₁' J}
  → {K₁₁' : IndexedFunctor C₁₁' E₁₁' K}
  → {K₂₁' : IndexedFunctor C₂₁' E₂₁' K}
  → {I₂₂' : IndexedFunctor D₂₂' E₂₂' (chain-functor-snoc I₂₁')}
  → {J₂₂' : IndexedFunctor C₂₂' D₂₂' (chain-functor-snoc J₂₁')}
  → {K₂₂' : IndexedFunctor C₂₂' E₂₂' (chain-functor-snoc K₂₁')}
  → (s₁ : IndexedSplitFunctorSquare I₁₁' I₂₁' G₁ H₁)
  → (t₁ : IndexedSplitFunctorSquare J₁₁' J₂₁' F₁ G₁)
  → (u₁ : IndexedSplitFunctorSquare K₁₁' K₂₁' F₁ H₁)
  → IndexedFunctorCompose I₁₁' J₁₁' K₁₁'
  → IndexedFunctorCompose I₂₂' J₂₂' K₂₂'
  → IndexedFunctorCompose
    (indexed-functor-sigma-sum I₂₂' s₁)
    (indexed-functor-sigma-sum J₂₂' t₁)
    (indexed-functor-sigma-sum K₂₂' u₁)

indexed-functor-compose-sigma-sum-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {D₁₁' D₂₁' : IndexedCategory D}
  → (E₁₁' E₂₁' : (x : A) → IndexedCategory (E x))
  → {C₂₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → {D₂₂' : IndexedCategory (chain-category-snoc D₂₁')}
  → (E₂₂' : (x : A) → IndexedCategory (chain-category-snoc (E₂₁' x)))
  → {F₁ : IndexedSplitFunctor C₁₁' C₂₁'}
  → {G₁ : IndexedSplitFunctor D₁₁' D₂₁'}
  → (H₁ : (x : A) → IndexedSplitFunctor (E₁₁' x) (E₂₁' x))
  → {I : ChainFunctor D (E x₁)}
  → {J : ChainFunctor C D}
  → {K : ChainFunctor C (E x₂)}
  → {I₁₁' : IndexedFunctor D₁₁' (E₁₁' x₁) I}
  → {I₂₁' : IndexedFunctor D₂₁' (E₂₁' x₁) I}
  → {J₁₁' : IndexedFunctor C₁₁' D₁₁' J}
  → {J₂₁' : IndexedFunctor C₂₁' D₂₁' J}
  → {K₁₁' : IndexedFunctor C₁₁' (E₁₁' x₂) K}
  → {K₂₁' : IndexedFunctor C₂₁' (E₂₁' x₂) K}
  → {I₂₂' : IndexedFunctor D₂₂' (E₂₂' x₁) (chain-functor-snoc I₂₁')}
  → {J₂₂' : IndexedFunctor C₂₂' D₂₂' (chain-functor-snoc J₂₁')}
  → {K₂₂' : IndexedFunctor C₂₂' (E₂₂' x₂) (chain-functor-snoc K₂₁')}
  → (s₁ : IndexedSplitFunctorSquare I₁₁' I₂₁' G₁ (H₁ x₁))
  → (t₁ : IndexedSplitFunctorSquare J₁₁' J₂₁' F₁ G₁)
  → (u₁ : IndexedSplitFunctorSquare K₁₁' K₂₁' F₁ (H₁ x₂))
  → x₂ ≡ x₁
  → IndexedFunctorCompose I₁₁' J₁₁' K₁₁'
  → IndexedFunctorCompose I₂₂' J₂₂' K₂₂'
  → IndexedFunctorCompose
    (indexed-functor-sigma-sum I₂₂' s₁)
    (indexed-functor-sigma-sum J₂₂' t₁)
    (indexed-functor-sigma-sum K₂₂' u₁)

-- ### IndexedFunctorSquare

indexed-functor-square-sigma-sum
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁₁₁' C₁₂₁' : IndexedCategory C₁}
  → {C₂₁₁' C₂₂₁' : IndexedCategory C₂}
  → {D₁₁₁' D₁₂₁' : IndexedCategory D₁}
  → {D₂₁₁' D₂₂₁' : IndexedCategory D₂}
  → {C₁₂₂' : IndexedCategory (chain-category-snoc C₁₂₁')}
  → {C₂₂₂' : IndexedCategory (chain-category-snoc C₂₂₁')}
  → {D₁₂₂' : IndexedCategory (chain-category-snoc D₁₂₁')}
  → {D₂₂₂' : IndexedCategory (chain-category-snoc D₂₂₁')}
  → {F₁₁ : IndexedSplitFunctor C₁₁₁' C₁₂₁'}
  → {F₂₁ : IndexedSplitFunctor C₂₁₁' C₂₂₁'}
  → {G₁₁ : IndexedSplitFunctor D₁₁₁' D₁₂₁'}
  → {G₂₁ : IndexedSplitFunctor D₂₁₁' D₂₂₁'}
  → {H : ChainFunctor C₁ C₂}
  → {I : ChainFunctor D₁ D₂}
  → {J₁ : ChainFunctor C₁ D₁}
  → {J₂ : ChainFunctor C₂ D₂}
  → {H₁₁' : IndexedFunctor C₁₁₁' C₂₁₁' H}
  → {H₂₁' : IndexedFunctor C₁₂₁' C₂₂₁' H}
  → {I₁₁' : IndexedFunctor D₁₁₁' D₂₁₁' I}
  → {I₂₁' : IndexedFunctor D₁₂₁' D₂₂₁' I}
  → {J₁₁₁' : IndexedFunctor C₁₁₁' D₁₁₁' J₁}
  → {J₁₂₁' : IndexedFunctor C₁₂₁' D₁₂₁' J₁}
  → {J₂₁₁' : IndexedFunctor C₂₁₁' D₂₁₁' J₂}
  → {J₂₂₁' : IndexedFunctor C₂₂₁' D₂₂₁' J₂}
  → {H₂₂' : IndexedFunctor C₁₂₂' C₂₂₂' (chain-functor-snoc H₂₁')}
  → {I₂₂' : IndexedFunctor D₁₂₂' D₂₂₂' (chain-functor-snoc I₂₁')}
  → {J₁₂₂' : IndexedFunctor C₁₂₂' D₁₂₂' (chain-functor-snoc J₁₂₁')}
  → {J₂₂₂' : IndexedFunctor C₂₂₂' D₂₂₂' (chain-functor-snoc J₂₂₁')}
  → (s₁ : IndexedSplitFunctorSquare H₁₁' H₂₁' F₁₁ F₂₁)
  → (t₁ : IndexedSplitFunctorSquare I₁₁' I₂₁' G₁₁ G₂₁)
  → (u₁₁ : IndexedSplitFunctorSquare J₁₁₁' J₁₂₁' F₁₁ G₁₁)
  → (u₂₁ : IndexedSplitFunctorSquare J₂₁₁' J₂₂₁' F₂₁ G₂₁)
  → IndexedFunctorSquare H₁₁' I₁₁' J₁₁₁' J₂₁₁'
  → IndexedFunctorSquare H₂₂' I₂₂' J₁₂₂' J₂₂₂'
  → IndexedFunctorSquare
    (indexed-functor-sigma-sum H₂₂' s₁)
    (indexed-functor-sigma-sum I₂₂' t₁)
    (indexed-functor-sigma-sum J₁₂₂' u₁₁)
    (indexed-functor-sigma-sum J₂₂₂' u₂₁)

indexed-functor-square-sigma-sum-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁₁₁' C₁₂₁' : IndexedCategory C₁}
  → {C₂₁₁' C₂₂₁' : IndexedCategory C₂}
  → {D₁₁₁' D₁₂₁' : IndexedCategory D₁}
  → (D₂₁₁' D₂₂₁' : (x : A) → IndexedCategory (D₂ x))
  → {C₁₂₂' : IndexedCategory (chain-category-snoc C₁₂₁')}
  → {C₂₂₂' : IndexedCategory (chain-category-snoc C₂₂₁')}
  → {D₁₂₂' : IndexedCategory (chain-category-snoc D₁₂₁')}
  → (D₂₂₂' : (x : A) → IndexedCategory (chain-category-snoc (D₂₂₁' x)))
  → {F₁₁ : IndexedSplitFunctor C₁₁₁' C₁₂₁'}
  → {F₂₁ : IndexedSplitFunctor C₂₁₁' C₂₂₁'}
  → {G₁₁ : IndexedSplitFunctor D₁₁₁' D₁₂₁'}
  → (G₂₁ : (x : A) → IndexedSplitFunctor (D₂₁₁' x) (D₂₂₁' x))
  → {H : ChainFunctor C₁ C₂}
  → {I : ChainFunctor D₁ (D₂ x₁)}
  → {J₁ : ChainFunctor C₁ D₁}
  → {J₂ : ChainFunctor C₂ (D₂ x₂)}
  → {H₁₁' : IndexedFunctor C₁₁₁' C₂₁₁' H}
  → {H₂₁' : IndexedFunctor C₁₂₁' C₂₂₁' H}
  → {I₁₁' : IndexedFunctor D₁₁₁' (D₂₁₁' x₁) I}
  → {I₂₁' : IndexedFunctor D₁₂₁' (D₂₂₁' x₁) I}
  → {J₁₁₁' : IndexedFunctor C₁₁₁' D₁₁₁' J₁}
  → {J₁₂₁' : IndexedFunctor C₁₂₁' D₁₂₁' J₁}
  → {J₂₁₁' : IndexedFunctor C₂₁₁' (D₂₁₁' x₂) J₂}
  → {J₂₂₁' : IndexedFunctor C₂₂₁' (D₂₂₁' x₂) J₂}
  → {H₂₂' : IndexedFunctor C₁₂₂' C₂₂₂' (chain-functor-snoc H₂₁')}
  → {I₂₂' : IndexedFunctor D₁₂₂' (D₂₂₂' x₁) (chain-functor-snoc I₂₁')}
  → {J₁₂₂' : IndexedFunctor C₁₂₂' D₁₂₂' (chain-functor-snoc J₁₂₁')}
  → {J₂₂₂' : IndexedFunctor C₂₂₂' (D₂₂₂' x₂) (chain-functor-snoc J₂₂₁')}
  → (s₁ : IndexedSplitFunctorSquare H₁₁' H₂₁' F₁₁ F₂₁)
  → (t₁ : IndexedSplitFunctorSquare I₁₁' I₂₁' G₁₁ (G₂₁ x₁))
  → (u₁₁ : IndexedSplitFunctorSquare J₁₁₁' J₁₂₁' F₁₁ G₁₁)
  → (u₂₁ : IndexedSplitFunctorSquare J₂₁₁' J₂₂₁' F₂₁ (G₂₁ x₂))
  → x₂ ≡ x₁
  → IndexedFunctorSquare H₁₁' I₁₁' J₁₁₁' J₂₁₁'
  → IndexedFunctorSquare H₂₂' I₂₂' J₁₂₂' J₂₂₂'
  → IndexedFunctorSquare
    (indexed-functor-sigma-sum H₂₂' s₁)
    (indexed-functor-sigma-sum I₂₂' t₁)
    (indexed-functor-sigma-sum J₁₂₂' u₁₁)
    (indexed-functor-sigma-sum J₂₂₂' u₂₁)

-- ## Definitions

-- ### IndexedCategory

indexed-category-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  C₂₂' F₁
  = nil
    (category-sigma-sum
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      (indexed-category₁ C₂₂')
      (indexed-split-functor₀ F₁))
indexed-category-sigma-sum
  {n = suc _}
  {C = C}
  {C₁₁' = C₁₁'}
  C₂₂' F₁
  = cons
    (λ x → indexed-category-sigma-sum
      (IndexedCategory.tail C₂₂' x)
      (IndexedSplitFunctor.tail F₁ x))
    (λ f → indexed-functor-sigma-sum
      (IndexedCategory.indexed-functor C₂₂' f)
      (IndexedSplitFunctor.indexed-split-functor-square F₁ f))
    (λ x → indexed-functor-identity-sigma-sum
      (IndexedSplitFunctor.indexed-split-functor-square F₁
        (ChainCategory.identity C x))
      (IndexedCategory.indexed-functor-identity C₁₁' x)
      (IndexedCategory.indexed-functor-identity C₂₂' x))
    (λ f g → indexed-functor-compose-sigma-sum
      (IndexedSplitFunctor.indexed-split-functor-square F₁ f)
      (IndexedSplitFunctor.indexed-split-functor-square F₁ g)
      (IndexedSplitFunctor.indexed-split-functor-square F₁
        (ChainCategory.compose C f g))
      (IndexedCategory.indexed-functor-compose C₁₁' f g)
      (IndexedCategory.indexed-functor-compose C₂₂' f g))

-- ### IndexedFunctor

indexed-functor-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {D₁₁' = D₁₁'} {D₂₁' = D₂₁'}
  {C₂₂' = C₂₂'} {D₂₂' = D₂₂'}
  {F₁ = F₁} {G₁ = G₁}
  {H₁₁' = H₁₁'}
  H₂₂' s₁
  = nil
    (functor-sigma-sum
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {C₂₂ = indexed-category₁ C₂₂'}
      {D₂₂ = indexed-category₁ D₂₂'}
      {F₁ = indexed-split-functor₀ F₁}
      {G₁ = indexed-split-functor₀ G₁}
      {H₁₁ = indexed-functor₀ H₁₁'}
      (indexed-functor₁ H₂₂')
      (indexed-split-functor-square₀ s₁))
indexed-functor-sigma-sum
  {n = suc _}
  {F₁ = F₁} {G₁ = G₁} {H = H}
  {H₁₁' = H₁₁'}
  H₂₂' s₁
  = cons
    (λ x → indexed-functor-sigma-sum
      (IndexedFunctor.tail H₂₂' x)
      (IndexedSplitFunctorSquare.tail s₁ x))
    (λ {x = x} {y = y} f → indexed-functor-square-sigma-sum
      (IndexedSplitFunctor.indexed-split-functor-square F₁ f)
      (IndexedSplitFunctor.indexed-split-functor-square G₁
        (ChainFunctor.map H f))
      (IndexedSplitFunctorSquare.tail s₁ x)
      (IndexedSplitFunctorSquare.tail s₁ y)
      (IndexedFunctor.indexed-functor-square H₁₁' f)
      (IndexedFunctor.indexed-functor-square H₂₂' f))

-- ### IndexedFunctorIdentity

indexed-functor-identity-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {C₂₂' = C₂₂'}
  {F₁ = F₁}
  {G₁₁' = G₁₁'}
  {G₂₂' = G₂₂'}
  s₁ p₁₁ p₂₂
  = nil
    (functor-identity-sigma-sum
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {C₂₂ = indexed-category₁ C₂₂'}
      {F₁ = indexed-split-functor₀ F₁}
      {G₁₁ = indexed-functor₀ G₁₁'}
      {G₂₂ = indexed-functor₁ G₂₂'}
      (indexed-split-functor-square₀ s₁)
      (indexed-functor-identity₀ p₁₁)
      (indexed-functor-identity₁ p₂₂))
indexed-functor-identity-sigma-sum
  {n = suc _}
  {C = C}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {C₂₂' = C₂₂'}
  {F₁ = F₁}
  s₁ p₁₁ p₂₂
  = cons
    (IndexedFunctorIdentity.head p₁₁)
    (λ x → indexed-functor-identity-sigma-sum-eq
      (ChainCategory.tail C)
      (IndexedCategory.tail C₁₁')
      (IndexedCategory.tail C₂₁')
      (IndexedCategory.tail C₂₂')
      (IndexedSplitFunctor.tail F₁)
      (IndexedSplitFunctorSquare.tail s₁ x)
      (IndexedFunctorIdentity.base p₁₁ x)
      (IndexedFunctorIdentity.tail p₁₁ x)
      (IndexedFunctorIdentity.tail p₂₂ x))

indexed-functor-identity-sigma-sum-eq _ _ _ _ _ s₁ refl
  = indexed-functor-identity-sigma-sum s₁

-- ### IndexedFunctorCompose

indexed-functor-compose-sigma-sum
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
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {E₁₁ = indexed-category₀ E₁₁'}
      {E₂₁ = indexed-category₀ E₂₁'}
      {C₂₂ = indexed-category₁ C₂₂'}
      {D₂₂ = indexed-category₁ D₂₂'}
      {E₂₂ = indexed-category₁ E₂₂'}
      {I₁ = indexed-split-functor₀ F₁}
      {J₁ = indexed-split-functor₀ G₁}
      {K₁ = indexed-split-functor₀ H₁}
      {L₁₁ = indexed-functor₀ I₁₁'}
      {M₁₁ = indexed-functor₀ J₁₁'}
      {N₁₁ = indexed-functor₀ K₁₁'}
      {L₂₂ = indexed-functor₁ I₂₂'}
      {M₂₂ = indexed-functor₁ J₂₂'}
      {N₂₂ = indexed-functor₁ K₂₂'}
      (indexed-split-functor-square₀ s₁)
      (indexed-split-functor-square₀ t₁)
      (indexed-split-functor-square₀ u₁)
      (indexed-functor-compose₀ p₁₁)
      (indexed-functor-compose₁ p₂₂))
indexed-functor-compose-sigma-sum
  {n = suc _}
  {E = E}
  {E₁₁' = E₁₁'} {E₂₁' = E₂₁'}
  {E₂₂' = E₂₂'}
  {H₁ = H₁}
  {J = J}
  s₁ t₁ u₁ p₁₁ p₂₂
  = cons
    (IndexedFunctorCompose.head p₁₁)
    (λ x → indexed-functor-compose-sigma-sum-eq
      (ChainCategory.tail E)
      (IndexedCategory.tail E₁₁')
      (IndexedCategory.tail E₂₁')
      (IndexedCategory.tail E₂₂')
      (IndexedSplitFunctor.tail H₁)
      (IndexedSplitFunctorSquare.tail s₁ (ChainFunctor.base J x))
      (IndexedSplitFunctorSquare.tail t₁ x)
      (IndexedSplitFunctorSquare.tail u₁ x)
      (IndexedFunctorCompose.base p₁₁ x)
      (IndexedFunctorCompose.tail p₁₁ x)
      (IndexedFunctorCompose.tail p₂₂ x))

indexed-functor-compose-sigma-sum-eq _ _ _ _ _ s₁ t₁ u₁ refl
  = indexed-functor-compose-sigma-sum s₁ t₁ u₁

-- ### IndexedFunctorSquare

indexed-functor-square-sigma-sum
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
      {C₁₁₁ = indexed-category₀ C₁₁₁'}
      {C₁₂₁ = indexed-category₀ C₁₂₁'}
      {C₂₁₁ = indexed-category₀ C₂₁₁'}
      {C₂₂₁ = indexed-category₀ C₂₂₁'}
      {D₁₁₁ = indexed-category₀ D₁₁₁'}
      {D₁₂₁ = indexed-category₀ D₁₂₁'}
      {D₂₁₁ = indexed-category₀ D₂₁₁'}
      {D₂₂₁ = indexed-category₀ D₂₂₁'}
      {C₁₂₂ = indexed-category₁ C₁₂₂'}
      {C₂₂₂ = indexed-category₁ C₂₂₂'}
      {D₁₂₂ = indexed-category₁ D₁₂₂'}
      {D₂₂₂ = indexed-category₁ D₂₂₂'}
      {F₁₁ = indexed-split-functor₀ F₁₁}
      {F₂₁ = indexed-split-functor₀ F₂₁}
      {G₁₁ = indexed-split-functor₀ G₁₁}
      {G₂₁ = indexed-split-functor₀ G₂₁}
      {H₁₁ = indexed-functor₀ H₁₁'}
      {I₁₁ = indexed-functor₀ I₁₁'}
      {J₁₁₁ = indexed-functor₀ J₁₁₁'}
      {J₂₁₁ = indexed-functor₀ J₂₁₁'}
      {H₂₂ = indexed-functor₁ H₂₂'}
      {I₂₂ = indexed-functor₁ I₂₂'}
      {J₁₂₂ = indexed-functor₁ J₁₂₂'}
      {J₂₂₂ = indexed-functor₁ J₂₂₂'}
      (indexed-split-functor-square₀ s₁)
      (indexed-split-functor-square₀ t₁)
      (indexed-split-functor-square₀ u₁₁)
      (indexed-split-functor-square₀ u₂₁)
      (indexed-functor-square₀ s₁₁)
      (indexed-functor-square₁ s₂₂))
indexed-functor-square-sigma-sum
  {n = suc _}
  {D₂ = D₂}
  {D₂₁₁' = D₂₁₁'} {D₂₂₁' = D₂₂₁'}
  {D₂₂₂' = D₂₂₂'}
  {G₂₁ = G₂₁}
  {H = H} {J₁ = J₁}
  s₁ t₁ u₁₁ u₂₁ v₁₁ v₂₂
  = cons
    (IndexedFunctorSquare.head v₁₁)
    (λ x₁ → indexed-functor-square-sigma-sum-eq
      (ChainCategory.tail D₂)
      (IndexedCategory.tail D₂₁₁')
      (IndexedCategory.tail D₂₂₁')
      (IndexedCategory.tail D₂₂₂')
      (IndexedSplitFunctor.tail G₂₁)
      (IndexedSplitFunctorSquare.tail s₁ x₁)
      (IndexedSplitFunctorSquare.tail t₁ (ChainFunctor.base J₁ x₁))
      (IndexedSplitFunctorSquare.tail u₁₁ x₁)
      (IndexedSplitFunctorSquare.tail u₂₁ (ChainFunctor.base H x₁))
      (IndexedFunctorSquare.base v₁₁ x₁)
      (IndexedFunctorSquare.tail v₁₁ x₁)
      (IndexedFunctorSquare.tail v₂₂ x₁))

indexed-functor-square-sigma-sum-eq _ _ _ _ _ s₁ t₁ u₁₁ u₂₁ refl
  = indexed-functor-square-sigma-sum s₁ t₁ u₁₁ u₂₁

