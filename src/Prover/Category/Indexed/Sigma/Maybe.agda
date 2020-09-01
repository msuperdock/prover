module Prover.Category.Indexed.Sigma.Maybe where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedDependentFunctorCompose; IndexedDependentFunctorIdentity;
    IndexedDependentFunctorSquare; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; empty;
    indexed-category₀; indexed-dependent-category; indexed-dependent-category₀;
    indexed-dependent-functor; indexed-dependent-functor₀;
    indexed-dependent-functor-compose; indexed-dependent-functor-compose₀;
    indexed-dependent-functor-identity; indexed-dependent-functor-identity₀;
    indexed-dependent-functor-square; indexed-dependent-functor-square₀; sigma)
open import Prover.Category.Sigma.Maybe
  using (category-sigma-maybe; functor-compose-sigma-maybe;
    functor-identity-sigma-maybe; functor-sigma-maybe;
    functor-square-sigma-maybe)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-dependent-category-snoc;
    chain-dependent-functor-snoc; chain-functor-snoc)
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

-- ### IndexedDependentCategory

indexed-dependent-category-sigma-maybe
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → (C₁'' : IndexedDependentCategory C')
  → IndexedDependentCategory
    (chain-dependent-category-snoc C₁'')
  → IndexedDependentCategory C'

-- ### IndexedDependentFunctor

indexed-dependent-functor-sigma-maybe
  : {n : ℕ}
  → {C D : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {C₁'' : IndexedDependentCategory C'}
  → {D₁'' : IndexedDependentCategory D'}
  → {C₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₁'')}
  → {D₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₁'')}
  → {F : ChainDependentFunctor C' D'}
  → (F₁' : IndexedDependentFunctor C₁'' D₁'' F)
  → IndexedDependentFunctor C₂'' D₂''
    (chain-dependent-functor-snoc F₁')
  → IndexedDependentFunctor
    (indexed-dependent-category-sigma-maybe C₁'' C₂'')
    (indexed-dependent-category-sigma-maybe D₁'' D₂'') F

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-sigma-maybe
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C₁'' : IndexedDependentCategory C'}
  → {C₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₁'')}
  → {F : ChainDependentFunctor C' C'}
  → (F₁' : IndexedDependentFunctor C₁'' C₁'' F)
  → {F₂' : IndexedDependentFunctor C₂'' C₂''
    (chain-dependent-functor-snoc F₁')}
  → IndexedDependentFunctorIdentity F₂'
  → IndexedDependentFunctorIdentity
    (indexed-dependent-functor-sigma-maybe F₁' F₂')

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-sigma-maybe
  : {n : ℕ}
  → {C D E : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {E' : ChainDependentCategory E n}
  → {C₁'' : IndexedDependentCategory C'}
  → {D₁'' : IndexedDependentCategory D'}
  → {E₁'' : IndexedDependentCategory E'}
  → {C₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₁'')}
  → {D₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₁'')}
  → {E₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc E₁'')}
  → {F : ChainDependentFunctor D' E'}
  → {G : ChainDependentFunctor C' D'}
  → {H : ChainDependentFunctor C' E'}
  → (F₁' : IndexedDependentFunctor D₁'' E₁'' F)
  → (G₁' : IndexedDependentFunctor C₁'' D₁'' G)
  → (H₁' : IndexedDependentFunctor C₁'' E₁'' H)
  → {F₂' : IndexedDependentFunctor D₂'' E₂''
    (chain-dependent-functor-snoc F₁')}
  → {G₂' : IndexedDependentFunctor C₂'' D₂''
    (chain-dependent-functor-snoc G₁')}
  → {H₂' : IndexedDependentFunctor C₂'' E₂''
    (chain-dependent-functor-snoc H₁')}
  → IndexedDependentFunctorCompose F₂' G₂' H₂'
  → IndexedDependentFunctorCompose
    (indexed-dependent-functor-sigma-maybe F₁' F₂')
    (indexed-dependent-functor-sigma-maybe G₁' G₂')
    (indexed-dependent-functor-sigma-maybe H₁' H₂')

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-sigma-maybe
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : Category}
  → {C₁' : ChainDependentCategory C₁ n}
  → {C₂' : ChainDependentCategory C₂ n}
  → {D₁' : ChainDependentCategory D₁ n}
  → {D₂' : ChainDependentCategory D₂ n}
  → {C₁₁'' : IndexedDependentCategory C₁'}
  → {C₂₁'' : IndexedDependentCategory C₂'}
  → {D₁₁'' : IndexedDependentCategory D₁'}
  → {D₂₁'' : IndexedDependentCategory D₂'}
  → {C₁₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₁₁'')}
  → {C₂₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₂₁'')}
  → {D₁₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₁₁'')}
  → {D₂₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₂₁'')}
  → {F : ChainDependentFunctor C₁' C₂'}
  → {G : ChainDependentFunctor D₁' D₂'}
  → {H₁ : ChainDependentFunctor C₁' D₁'}
  → {H₂ : ChainDependentFunctor C₂' D₂'}
  → (F₁' : IndexedDependentFunctor C₁₁'' C₂₁'' F)
  → (G₁' : IndexedDependentFunctor D₁₁'' D₂₁'' G)
  → (H₁₁' : IndexedDependentFunctor C₁₁'' D₁₁'' H₁)
  → (H₂₁' : IndexedDependentFunctor C₂₁'' D₂₁'' H₂)
  → {F₂' : IndexedDependentFunctor C₁₂'' C₂₂''
    (chain-dependent-functor-snoc F₁')}
  → {G₂' : IndexedDependentFunctor D₁₂'' D₂₂''
    (chain-dependent-functor-snoc G₁')}
  → {H₁₂' : IndexedDependentFunctor C₁₂'' D₁₂''
    (chain-dependent-functor-snoc H₁₁')}
  → {H₂₂' : IndexedDependentFunctor C₂₂'' D₂₂''
    (chain-dependent-functor-snoc H₂₁')}
  → IndexedDependentFunctorSquare F₂' G₂' H₁₂' H₂₂'
  → IndexedDependentFunctorSquare
    (indexed-dependent-functor-sigma-maybe F₁' F₂')
    (indexed-dependent-functor-sigma-maybe G₁' G₂')
    (indexed-dependent-functor-sigma-maybe H₁₁' H₁₂')
    (indexed-dependent-functor-sigma-maybe H₂₁' H₂₂')

-- ## Definitions

-- ### IndexedCategory

indexed-category-sigma-maybe
  {n = zero} C₁' C₂'
  = empty
    (category-sigma-maybe
      {C₁ = indexed-category₀ C₁'}
      (indexed-dependent-category₀
        (IndexedCategory.unpack C₂')))
indexed-category-sigma-maybe
  {n = suc _} C₁' C₂'
  = sigma
    (indexed-dependent-category-sigma-maybe
      (IndexedCategory.unpack C₁')
      (IndexedCategory.unpack C₂'))

-- ### IndexedFunctor

indexed-functor-sigma-maybe
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'}
  {C₂' = C₂'} {D₂' = D₂'} _ F₂'
  = empty
    (functor-sigma-maybe
      {C₁ = indexed-category₀ C₁'}
      {D₁ = indexed-category₀ D₁'}
      {C₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂')}
      {D₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₂')}
      (indexed-dependent-functor₀
        (IndexedFunctor.unpack F₂')))
indexed-functor-sigma-maybe
  {n = suc _} F₁' F₂'
  = sigma
    (indexed-dependent-functor-sigma-maybe
      (IndexedFunctor.unpack F₁')
      (IndexedFunctor.unpack F₂'))

-- ### IndexedFunctorIdentity

indexed-functor-identity-sigma-maybe
  {n = zero}
  {C₁' = C₁'}
  {C₂' = C₂'} _
  {F₂' = F₂'} p₂
  = empty
    (functor-identity-sigma-maybe
      {C₁ = indexed-category₀ C₁'}
      {C₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂')}
      {F₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack F₂')}
      (indexed-dependent-functor-identity₀
        (IndexedFunctorIdentity.unpack p₂)))
indexed-functor-identity-sigma-maybe
  {n = suc _} F₁' p₂
  = sigma
    (indexed-dependent-functor-identity-sigma-maybe
      (IndexedFunctor.unpack F₁')
      (IndexedFunctorIdentity.unpack p₂))

indexed-functor-identity-sigma-maybe-eq _ _ _ F₁' refl
  = indexed-functor-identity-sigma-maybe F₁'

-- ### IndexedFunctorCompose

indexed-functor-compose-sigma-maybe
  {n = zero}
  {C₁' = C₁'} {D₁' = D₁'} {E₁' = E₁'}
  {C₂' = C₂'} {D₂' = D₂'} {E₂' = E₂'} _ _ _
  {F₂' = F₂'} {G₂' = G₂'} {H₂' = H₂'} p₂
  = empty
    (functor-compose-sigma-maybe
      {C₁ = indexed-category₀ C₁'}
      {D₁ = indexed-category₀ D₁'}
      {E₁ = indexed-category₀ E₁'}
      {C₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂')}
      {D₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₂')}
      {E₂ = indexed-dependent-category₀
        (IndexedCategory.unpack E₂')}
      {F₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack F₂')}
      {G₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack G₂')}
      {H₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack H₂')}
      (indexed-dependent-functor-compose₀
        (IndexedFunctorCompose.unpack p₂)))
indexed-functor-compose-sigma-maybe
  {n = suc _} F₁' G₁' H₁' p₂
  = sigma
    (indexed-dependent-functor-compose-sigma-maybe
      (IndexedFunctor.unpack F₁')
      (IndexedFunctor.unpack G₁')
      (IndexedFunctor.unpack H₁')
      (IndexedFunctorCompose.unpack p₂))

indexed-functor-compose-sigma-maybe-eq _ _ _ F₁' G₁' H₁' refl
  = indexed-functor-compose-sigma-maybe F₁' G₁' H₁'

-- ### IndexedFunctorSquare

indexed-functor-square-sigma-maybe
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'} {D₁₁' = D₁₁'} {D₂₁' = D₂₁'}
  {C₁₂' = C₁₂'} {C₂₂' = C₂₂'} {D₁₂' = D₁₂'} {D₂₂' = D₂₂'} _ _ _ _
  {F₂' = F₂'} {G₂' = G₂'} {H₁₂' = H₁₂'} {H₂₂' = H₂₂'} s₂
  = empty
    (functor-square-sigma-maybe
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {C₁₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₁₂')}
      {C₂₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂₂')}
      {D₁₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₁₂')}
      {D₂₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₂₂')}
      {F₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack F₂')}
      {G₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack G₂')}
      {H₁₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack H₁₂')}
      {H₂₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack H₂₂')}
      (indexed-dependent-functor-square₀
        (IndexedFunctorSquare.unpack s₂)))
indexed-functor-square-sigma-maybe
  {n = suc _} F₁' G₁' H₁₁' H₂₁' s₂
  = sigma
    (indexed-dependent-functor-square-sigma-maybe
      (IndexedFunctor.unpack F₁')
      (IndexedFunctor.unpack G₁')
      (IndexedFunctor.unpack H₁₁')
      (IndexedFunctor.unpack H₂₁')
      (IndexedFunctorSquare.unpack s₂))

indexed-functor-square-sigma-maybe-eq _ _ _ F₁' G₁' H₁₁' H₂₁' refl
  = indexed-functor-square-sigma-maybe F₁' G₁' H₁₁' H₂₁'

-- ### IndexedDependentCategory

indexed-dependent-category-sigma-maybe
  {C = C} C₁'' C₂''
  = indexed-dependent-category
    (λ x → indexed-category-sigma-maybe
      (IndexedDependentCategory.indexed-category C₁'' x)
      (IndexedDependentCategory.indexed-category C₂'' x))
    (λ f → indexed-functor-sigma-maybe
      (IndexedDependentCategory.indexed-functor C₁'' f)
      (IndexedDependentCategory.indexed-functor C₂'' f))
    (λ x → indexed-functor-identity-sigma-maybe
      (IndexedDependentCategory.indexed-functor C₁'' (Category.identity C x))
      (IndexedDependentCategory.indexed-functor-identity C₂'' x))
    (λ f g → indexed-functor-compose-sigma-maybe
      (IndexedDependentCategory.indexed-functor C₁'' f)
      (IndexedDependentCategory.indexed-functor C₁'' g)
      (IndexedDependentCategory.indexed-functor C₁'' (Category.compose C f g))
      (IndexedDependentCategory.indexed-functor-compose C₂'' f g))

-- ### IndexedDependentFunctor

indexed-dependent-functor-sigma-maybe
  {C₁'' = C₁''} {D₁'' = D₁''} {F = F} F₁' F₂'
  = indexed-dependent-functor
    (λ x → indexed-functor-sigma-maybe
      (IndexedDependentFunctor.indexed-functor F₁' x)
      (IndexedDependentFunctor.indexed-functor F₂' x))
    (λ {x = x} {y = y} f → indexed-functor-square-sigma-maybe
      (IndexedDependentCategory.indexed-functor C₁'' f)
      (IndexedDependentCategory.indexed-functor D₁''
        (ChainDependentFunctor.map F f))
      (IndexedDependentFunctor.indexed-functor F₁' x)
      (IndexedDependentFunctor.indexed-functor F₁' y)
      (IndexedDependentFunctor.indexed-functor-square F₂' f))

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-sigma-maybe
  {C' = C'} {C₁'' = C₁''} {C₂'' = C₂''} F₁' p₂
  = indexed-dependent-functor-identity
    (IndexedDependentFunctorIdentity.functor p₂)
    (λ x → indexed-functor-identity-sigma-maybe-eq
      (ChainDependentCategory.chain-category C')
      (IndexedDependentCategory.indexed-category C₁'')
      (IndexedDependentCategory.indexed-category C₂'')
      (IndexedDependentFunctor.indexed-functor F₁' x)
      (IndexedDependentFunctorIdentity.base p₂ x)
      (IndexedDependentFunctorIdentity.indexed-functor p₂ x))

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-sigma-maybe
  {E' = E'} {E₁'' = E₁''} {E₂'' = E₂''} {G = G} F₁' G₁' H₁' p₂
  = indexed-dependent-functor-compose
    (IndexedDependentFunctorCompose.functor p₂)
    (λ x → indexed-functor-compose-sigma-maybe-eq
      (ChainDependentCategory.chain-category E')
      (IndexedDependentCategory.indexed-category E₁'')
      (IndexedDependentCategory.indexed-category E₂'')
      (IndexedDependentFunctor.indexed-functor F₁'
        (ChainDependentFunctor.base G x))
      (IndexedDependentFunctor.indexed-functor G₁' x)
      (IndexedDependentFunctor.indexed-functor H₁' x)
      (IndexedDependentFunctorCompose.base p₂ x)
      (IndexedDependentFunctorCompose.indexed-functor p₂ x))

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-sigma-maybe
  {D₂' = D₂'} {D₂₁'' = D₂₁''} {D₂₂'' = D₂₂''} {F = F} {H₁ = H₁}
  F₁' G₁' H₁₁' H₂₁' s₂
  = indexed-dependent-functor-square
    (IndexedDependentFunctorSquare.functor s₂)
    (λ x₁ → indexed-functor-square-sigma-maybe-eq
      (ChainDependentCategory.chain-category D₂')
      (IndexedDependentCategory.indexed-category D₂₁'')
      (IndexedDependentCategory.indexed-category D₂₂'')
      (IndexedDependentFunctor.indexed-functor F₁' x₁)
      (IndexedDependentFunctor.indexed-functor G₁'
        (ChainDependentFunctor.base H₁ x₁))
      (IndexedDependentFunctor.indexed-functor H₁₁' x₁)
      (IndexedDependentFunctor.indexed-functor H₂₁'
        (ChainDependentFunctor.base F x₁))
      (IndexedDependentFunctorSquare.base s₂ x₁)
      (IndexedDependentFunctorSquare.indexed-functor s₂ x₁))

