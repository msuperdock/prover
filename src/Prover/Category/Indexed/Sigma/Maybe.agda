module Prover.Category.Indexed.Sigma.Maybe where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; cons; indexed-category₀;
    indexed-category₁; indexed-functor₁; indexed-functor-compose₁;
    indexed-functor-identity₁; indexed-functor-square₁; nil)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-maybe; functor-compose-sigma-maybe;
    functor-identity-sigma-maybe; functor-sigma-maybe;
    functor-square-sigma-maybe)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-functor-snoc)
open import Prover.Prelude

-- ## Types

-- ### IndexedCategory

indexed-category-sigma-maybe
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : IndexedCategory C)
  → IndexedCategory
    (chain-category-snoc C₁')
  → IndexedCategory C

-- ### IndexedFunctor

indexed-functor-sigma-maybe
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁' : IndexedCategory C}
  → {D₁' : IndexedCategory D}
  → {C₂' : IndexedCategory
    (chain-category-snoc C₁')}
  → {D₂' : IndexedCategory
    (chain-category-snoc D₁')}
  → {F : ChainFunctor C D}
  → (F₁' : IndexedFunctor C₁' D₁' F)
  → IndexedFunctor C₂' D₂'
    (chain-functor-snoc F₁')
  → IndexedFunctor
    (indexed-category-sigma-maybe C₁' C₂')
    (indexed-category-sigma-maybe D₁' D₂') F

-- ### IndexedFunctorIdentity

indexed-functor-identity-sigma-maybe
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : IndexedCategory C}
  → {C₂' : IndexedCategory
    (chain-category-snoc C₁')}
  → {F : ChainFunctor C C}
  → (F₁' : IndexedFunctor C₁' C₁' F)
  → {F₂' : IndexedFunctor C₂' C₂'
    (chain-functor-snoc F₁')}
  → IndexedFunctorIdentity F₂'
  → IndexedFunctorIdentity
    (indexed-functor-sigma-maybe F₁' F₂')

indexed-functor-identity-sigma-maybe-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁' : (x : A) → IndexedCategory (C x))
  → (C₂' : (x : A) → IndexedCategory
    (chain-category-snoc (C₁' x)))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → (F₁' : IndexedFunctor (C₁' x₁) (C₁' x₂) F)
  → {F₂' : IndexedFunctor (C₂' x₁) (C₂' x₂)
    (chain-functor-snoc F₁')}
  → x₂ ≡ x₁
  → IndexedFunctorIdentity F₂'
  → IndexedFunctorIdentity
    (indexed-functor-sigma-maybe F₁' F₂')

-- ### IndexedFunctorCompose

indexed-functor-compose-sigma-maybe
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C₁' : IndexedCategory C}
  → {D₁' : IndexedCategory D}
  → {E₁' : IndexedCategory E}
  → {C₂' : IndexedCategory
    (chain-category-snoc C₁')}
  → {D₂' : IndexedCategory
    (chain-category-snoc D₁')}
  → {E₂' : IndexedCategory
    (chain-category-snoc E₁')}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → (F₁' : IndexedFunctor D₁' E₁' F)
  → (G₁' : IndexedFunctor C₁' D₁' G)
  → (H₁' : IndexedFunctor C₁' E₁' H)
  → {F₂' : IndexedFunctor D₂' E₂'
    (chain-functor-snoc F₁')}
  → {G₂' : IndexedFunctor C₂' D₂'
    (chain-functor-snoc G₁')}
  → {H₂' : IndexedFunctor C₂' E₂'
    (chain-functor-snoc H₁')}
  → IndexedFunctorCompose F₂' G₂' H₂'
  → IndexedFunctorCompose
    (indexed-functor-sigma-maybe F₁' F₂')
    (indexed-functor-sigma-maybe G₁' G₂')
    (indexed-functor-sigma-maybe H₁' H₂')

indexed-functor-compose-sigma-maybe-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C₁' : IndexedCategory C}
  → {D₁' : IndexedCategory D}
  → (E₁' : (x : A) → IndexedCategory (E x))
  → {C₂' : IndexedCategory (chain-category-snoc C₁')}
  → {D₂' : IndexedCategory (chain-category-snoc D₁')}
  → (E₂' : (x : A) → IndexedCategory (chain-category-snoc (E₁' x)))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → (F₁' : IndexedFunctor D₁' (E₁' x₁) F)
  → (G₁' : IndexedFunctor C₁' D₁' G)
  → (H₁' : IndexedFunctor C₁' (E₁' x₂) H)
  → {F₂' : IndexedFunctor D₂' (E₂' x₁) (chain-functor-snoc F₁')}
  → {G₂' : IndexedFunctor C₂' D₂' (chain-functor-snoc G₁')}
  → {H₂' : IndexedFunctor C₂' (E₂' x₂) (chain-functor-snoc H₁')}
  → x₂ ≡ x₁
  → IndexedFunctorCompose F₂' G₂' H₂'
  → IndexedFunctorCompose
    (indexed-functor-sigma-maybe F₁' F₂')
    (indexed-functor-sigma-maybe G₁' G₂')
    (indexed-functor-sigma-maybe H₁' H₂')

-- ### IndexedFunctorSquare

indexed-functor-square-sigma-maybe
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁₁' : IndexedCategory C₁}
  → {C₂₁' : IndexedCategory C₂}
  → {D₁₁' : IndexedCategory D₁}
  → {D₂₁' : IndexedCategory D₂}
  → {C₁₂' : IndexedCategory
    (chain-category-snoc C₁₁')}
  → {C₂₂' : IndexedCategory
    (chain-category-snoc C₂₁')}
  → {D₁₂' : IndexedCategory
    (chain-category-snoc D₁₁')}
  → {D₂₂' : IndexedCategory
    (chain-category-snoc D₂₁')}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → (F₁' : IndexedFunctor C₁₁' C₂₁' F)
  → (G₁' : IndexedFunctor D₁₁' D₂₁' G)
  → (H₁₁' : IndexedFunctor C₁₁' D₁₁' H₁)
  → (H₂₁' : IndexedFunctor C₂₁' D₂₁' H₂)
  → {F₂' : IndexedFunctor C₁₂' C₂₂'
    (chain-functor-snoc F₁')}
  → {G₂' : IndexedFunctor D₁₂' D₂₂'
    (chain-functor-snoc G₁')}
  → {H₁₂' : IndexedFunctor C₁₂' D₁₂'
    (chain-functor-snoc H₁₁')}
  → {H₂₂' : IndexedFunctor C₂₂' D₂₂'
    (chain-functor-snoc H₂₁')}
  → IndexedFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → IndexedFunctorSquare
    (indexed-functor-sigma-maybe F₁' F₂')
    (indexed-functor-sigma-maybe G₁' G₂')
    (indexed-functor-sigma-maybe H₁₁' H₁₂')
    (indexed-functor-sigma-maybe H₂₁' H₂₂')

indexed-functor-square-sigma-maybe-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁₁' : IndexedCategory C₁}
  → {C₂₁' : IndexedCategory C₂}
  → {D₁₁' : IndexedCategory D₁}
  → (D₂₁' : (x : A) → IndexedCategory (D₂ x))
  → {C₁₂' : IndexedCategory (chain-category-snoc C₁₁')}
  → {C₂₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → {D₁₂' : IndexedCategory (chain-category-snoc D₁₁')}
  → (D₂₂' : (x : A) → IndexedCategory (chain-category-snoc (D₂₁' x)))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → (F₁' : IndexedFunctor C₁₁' C₂₁' F)
  → (G₁' : IndexedFunctor D₁₁' (D₂₁' x₁) G)
  → (H₁₁' : IndexedFunctor C₁₁' D₁₁' H₁)
  → (H₂₁' : IndexedFunctor C₂₁' (D₂₁' x₂) H₂)
  → {F₂' : IndexedFunctor C₁₂' C₂₂' (chain-functor-snoc F₁')}
  → {G₂' : IndexedFunctor D₁₂' (D₂₂' x₁) (chain-functor-snoc G₁')}
  → {H₁₂' : IndexedFunctor C₁₂' D₁₂' (chain-functor-snoc H₁₁')}
  → {H₂₂' : IndexedFunctor C₂₂' (D₂₂' x₂) (chain-functor-snoc H₂₁')}
  → x₂ ≡ x₁
  → IndexedFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → IndexedFunctorSquare
    (indexed-functor-sigma-maybe F₁' F₂')
    (indexed-functor-sigma-maybe G₁' G₂')
    (indexed-functor-sigma-maybe H₁₁' H₁₂')
    (indexed-functor-sigma-maybe H₂₁' H₂₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-sigma-maybe
  {n = zero} C₁' C₂'
  = nil
    (category-sigma-maybe
      {C₁ = indexed-category₀ C₁'}
      (indexed-category₁ C₂'))
indexed-category-sigma-maybe
  {n = suc _}
  {C = C} C₁' C₂'
  = cons
    (λ x → indexed-category-sigma-maybe
      (IndexedCategory.tail C₁' x)
      (IndexedCategory.tail C₂' x))
    (λ f → indexed-functor-sigma-maybe
      (IndexedCategory.indexed-functor C₁' f)
      (IndexedCategory.indexed-functor C₂' f))
    (λ x → indexed-functor-identity-sigma-maybe
      (IndexedCategory.indexed-functor C₁' (ChainCategory.identity C x))
      (IndexedCategory.indexed-functor-identity C₂' x))
    (λ f g → indexed-functor-compose-sigma-maybe
      (IndexedCategory.indexed-functor C₁' f)
      (IndexedCategory.indexed-functor C₁' g)
      (IndexedCategory.indexed-functor C₁' (ChainCategory.compose C f g))
      (IndexedCategory.indexed-functor-compose C₂' f g))

-- ### IndexedFunctor

indexed-functor-sigma-maybe
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'}
  {C₂' = C₂'} {D₂' = D₂'} _ F₂'
  = nil
    (functor-sigma-maybe
      {C₁ = indexed-category₀ C₁'}
      {D₁ = indexed-category₀ D₁'}
      {C₂ = indexed-category₁ C₂'}
      {D₂ = indexed-category₁ D₂'}
      (indexed-functor₁ F₂'))
indexed-functor-sigma-maybe
  {n = suc _}
  {C₁' = C₁'} {D₁' = D₁'}
  {F = F} F₁' F₂'
  = cons
    (λ x → indexed-functor-sigma-maybe
      (IndexedFunctor.tail F₁' x)
      (IndexedFunctor.tail F₂' x))
    (λ {x = x} {y = y} f → indexed-functor-square-sigma-maybe
      (IndexedCategory.indexed-functor C₁' f)
      (IndexedCategory.indexed-functor D₁' (ChainFunctor.map F f))
      (IndexedFunctor.tail F₁' x)
      (IndexedFunctor.tail F₁' y)
      (IndexedFunctor.indexed-functor-square F₂' f))

-- ### IndexedFunctorIdentity

indexed-functor-identity-sigma-maybe
  {n = zero}
  {C₁' = C₁'}
  {C₂' = C₂'} _
  {F₂' = F₂'} p₂
  = nil
    (functor-identity-sigma-maybe
      {C₁ = indexed-category₀ C₁'}
      {C₂ = indexed-category₁ C₂'}
      {F₂ = indexed-functor₁ F₂'}
      (indexed-functor-identity₁ p₂))
indexed-functor-identity-sigma-maybe
  {n = suc _}
  {C = C}
  {C₁' = C₁'}
  {C₂' = C₂'} F₁' p₂
  = cons
    (IndexedFunctorIdentity.head p₂)
    (λ x → indexed-functor-identity-sigma-maybe-eq
      (ChainCategory.tail C)
      (IndexedCategory.tail C₁')
      (IndexedCategory.tail C₂')
      (IndexedFunctor.tail F₁' x)
      (IndexedFunctorIdentity.base p₂ x)
      (IndexedFunctorIdentity.tail p₂ x))

indexed-functor-identity-sigma-maybe-eq _ _ _ F₁' refl
  = indexed-functor-identity-sigma-maybe F₁'

-- ### IndexedFunctorCompose

indexed-functor-compose-sigma-maybe
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'} {E₁' = E₁'}
  {C₂' = C₂'} {D₂' = D₂'} {E₂' = E₂'} _ _ _
  {F₂' = F₂'} {G₂' = G₂'} {H₂' = H₂'} p₂
  = nil
    (functor-compose-sigma-maybe
      {C₁ = indexed-category₀ C₁'}
      {D₁ = indexed-category₀ D₁'}
      {E₁ = indexed-category₀ E₁'}
      {C₂ = indexed-category₁ C₂'}
      {D₂ = indexed-category₁ D₂'}
      {E₂ = indexed-category₁ E₂'}
      {F₂ = indexed-functor₁ F₂'}
      {G₂ = indexed-functor₁ G₂'}
      {H₂ = indexed-functor₁ H₂'}
      (indexed-functor-compose₁ p₂))
indexed-functor-compose-sigma-maybe
  {n = suc _}
  {E = E}
  {E₁' = E₁'}
  {E₂' = E₂'}
  {G = G} F₁' G₁' H₁' p₂
  = cons
    (IndexedFunctorCompose.head p₂)
    (λ x → indexed-functor-compose-sigma-maybe-eq
      (ChainCategory.tail E)
      (IndexedCategory.tail E₁')
      (IndexedCategory.tail E₂')
      (IndexedFunctor.tail F₁' (ChainFunctor.base G x))
      (IndexedFunctor.tail G₁' x)
      (IndexedFunctor.tail H₁' x)
      (IndexedFunctorCompose.base p₂ x)
      (IndexedFunctorCompose.tail p₂ x))

indexed-functor-compose-sigma-maybe-eq _ _ _ F₁' G₁' H₁' refl
  = indexed-functor-compose-sigma-maybe F₁' G₁' H₁'

-- ### IndexedFunctorSquare

indexed-functor-square-sigma-maybe
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'} {D₁₁' = D₁₁'} {D₂₁' = D₂₁'}
  {C₁₂' = C₁₂'} {C₂₂' = C₂₂'} {D₁₂' = D₁₂'} {D₂₂' = D₂₂'} _ _ _ _
  {F₂' = F₂'} {G₂' = G₂'} {H₁₂' = H₁₂'} {H₂₂' = H₂₂'} s₂
  = nil
    (functor-square-sigma-maybe
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {C₁₂ = indexed-category₁ C₁₂'}
      {C₂₂ = indexed-category₁ C₂₂'}
      {D₁₂ = indexed-category₁ D₁₂'}
      {D₂₂ = indexed-category₁ D₂₂'}
      {F₂ = indexed-functor₁ F₂'}
      {G₂ = indexed-functor₁ G₂'}
      {H₁₂ = indexed-functor₁ H₁₂'}
      {H₂₂ = indexed-functor₁ H₂₂'}
      (indexed-functor-square₁ s₂))
indexed-functor-square-sigma-maybe
  {n = suc _}
  {D₂ = D₂}
  {D₂₁' = D₂₁'} {D₂₂' = D₂₂'}
  {F = F} {H₁ = H₁} F₁' G₁' H₁₁' H₂₁' s₂
  = cons
    (IndexedFunctorSquare.head s₂)
    (λ x₁ → indexed-functor-square-sigma-maybe-eq
      (ChainCategory.tail D₂)
      (IndexedCategory.tail D₂₁')
      (IndexedCategory.tail D₂₂')
      (IndexedFunctor.tail F₁' x₁)
      (IndexedFunctor.tail G₁' (ChainFunctor.base H₁ x₁))
      (IndexedFunctor.tail H₁₁' x₁)
      (IndexedFunctor.tail H₂₁' (ChainFunctor.base F x₁))
      (IndexedFunctorSquare.base s₂ x₁)
      (IndexedFunctorSquare.tail s₂ x₁))

indexed-functor-square-sigma-maybe-eq _ _ _ F₁' G₁' H₁₁' H₂₁' refl
  = indexed-functor-square-sigma-maybe F₁' G₁' H₁₁' H₂₁'

