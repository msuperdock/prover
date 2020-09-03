module Prover.Category.Snoc where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorIdentity;
    ChainFunctorSquare; chain-category₁; chain-functor₁; chain-functor-compose₁;
    chain-functor-identity₁; chain-functor-square₁; cons)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; indexed-category₀;
    indexed-functor₀; indexed-functor-compose₀; indexed-functor-identity₀;
    indexed-functor-square₀)
open import Prover.Prelude

-- ## Types

-- ### ChainCategory

chain-category-snoc
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedCategory C
  → ChainCategory (suc n)

-- ### ChainFunctor

chain-functor-snoc
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : IndexedCategory C}
  → {D' : IndexedCategory D}
  → {F : ChainFunctor C D}
  → IndexedFunctor C' D' F
  → ChainFunctor
    (chain-category-snoc C')
    (chain-category-snoc D')

-- ### ChainFunctorIdentity

chain-functor-identity-snoc
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedCategory C}
  → {F : ChainFunctor C C}
  → {F' : IndexedFunctor C' C' F}
  → IndexedFunctorIdentity F'
  → ChainFunctorIdentity
    (chain-functor-snoc F')

chain-functor-identity-snoc-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → IndexedCategory (C x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : IndexedFunctor (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → IndexedFunctorIdentity F'
  → ChainFunctorIdentity
    (chain-functor-snoc F')

-- ### ChainFunctorCompose

chain-functor-compose-snoc
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : IndexedCategory C}
  → {D' : IndexedCategory D}
  → {E' : IndexedCategory E}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : IndexedFunctor D' E' F}
  → {G' : IndexedFunctor C' D' G}
  → {H' : IndexedFunctor C' E' H}
  → IndexedFunctorCompose F' G' H'
  → ChainFunctorCompose
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H')

chain-functor-compose-snoc-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C' : IndexedCategory C}
  → {D' : IndexedCategory D}
  → (E' : (x : A) → IndexedCategory (E x))
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F' : IndexedFunctor D' (E' x₁) F}
  → {G' : IndexedFunctor C' D' G}
  → {H' : IndexedFunctor C' (E' x₂) H}
  → x₂ ≡ x₁
  → IndexedFunctorCompose F' G' H'
  → ChainFunctorCompose
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H')

-- ### ChainFunctorSquare

chain-functor-square-snoc
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : IndexedCategory C₁}
  → {C₂' : IndexedCategory C₂}
  → {D₁' : IndexedCategory D₁}
  → {D₂' : IndexedCategory D₂}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : IndexedFunctor C₁' C₂' F}
  → {G' : IndexedFunctor D₁' D₂' G}
  → {H₁' : IndexedFunctor C₁' D₁' H₁}
  → {H₂' : IndexedFunctor C₂' D₂' H₂}
  → IndexedFunctorSquare F' G' H₁' H₂'
  → ChainFunctorSquare
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H₁')
    (chain-functor-snoc H₂')

chain-functor-square-snoc-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁' : IndexedCategory C₁}
  → {C₂' : IndexedCategory C₂}
  → {D₁' : IndexedCategory D₁}
  → (D₂' : (x : A) → IndexedCategory (D₂ x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F' : IndexedFunctor C₁' C₂' F}
  → {G' : IndexedFunctor D₁' (D₂' x₁) G}
  → {H₁' : IndexedFunctor C₁' D₁' H₁}
  → {H₂' : IndexedFunctor C₂' (D₂' x₂) H₂}
  → x₂ ≡ x₁
  → IndexedFunctorSquare F' G' H₁' H₂'
  → ChainFunctorSquare
    (chain-functor-snoc F')
    (chain-functor-snoc G')
    (chain-functor-snoc H₁')
    (chain-functor-snoc H₂')

-- ## Definitions

-- ### ChainCategory

chain-category-snoc
  {n = zero} C'
  = chain-category₁
    (indexed-category₀ C')
chain-category-snoc
  {n = suc _} {C = C} C'
  = cons
    (ChainCategory.head C)
    (λ x → chain-category-snoc
      (IndexedCategory.tail C' x))
    (λ f → chain-functor-snoc
      (IndexedCategory.indexed-functor C' f))
    (λ x → chain-functor-identity-snoc
      (IndexedCategory.indexed-functor-identity C' x))
    (λ f g → chain-functor-compose-snoc
      (IndexedCategory.indexed-functor-compose C' f g))

-- ### ChainFunctor

chain-functor-snoc
  {n = zero} F'
  = chain-functor₁
    (indexed-functor₀ F')
chain-functor-snoc
  {n = suc _} {F = F} F'
  = cons
    (ChainFunctor.head F)
    (λ x → chain-functor-snoc
      (IndexedFunctor.tail F' x))
    (λ f → chain-functor-square-snoc
      (IndexedFunctor.indexed-functor-square F' f))

-- ### ChainFunctorIdentity

chain-functor-identity-snoc
  {n = zero} p
  = chain-functor-identity₁
    (indexed-functor-identity₀ p)
chain-functor-identity-snoc
  {n = suc _} {C = C} {C' = C'} p
  = cons
    (IndexedFunctorIdentity.head p)
    (λ x → chain-functor-identity-snoc-eq
      (ChainCategory.tail C)
      (IndexedCategory.tail C')
      (IndexedFunctorIdentity.base p x)
      (IndexedFunctorIdentity.tail p x))

chain-functor-identity-snoc-eq _ _ refl
  = chain-functor-identity-snoc

-- ### ChainFunctorCompose

chain-functor-compose-snoc
  {n = zero} p
  = chain-functor-compose₁
    (indexed-functor-compose₀ p)
chain-functor-compose-snoc
  {n = suc _} {E = E} {E' = E'} p
  = cons
    (IndexedFunctorCompose.head p)
    (λ x → chain-functor-compose-snoc-eq
      (ChainCategory.tail E)
      (IndexedCategory.tail E')
      (IndexedFunctorCompose.base p x)
      (IndexedFunctorCompose.tail p x))

chain-functor-compose-snoc-eq _ _ refl
  = chain-functor-compose-snoc

-- ### ChainFunctorSquare

chain-functor-square-snoc
  {n = zero} s
  = chain-functor-square₁
    (indexed-functor-square₀ s)
chain-functor-square-snoc
  {n = suc _} {D₂ = D₂} {D₂' = D₂'} s
  = cons
    (IndexedFunctorSquare.head s)
    (λ x₁ → chain-functor-square-snoc-eq
      (ChainCategory.tail D₂)
      (IndexedCategory.tail D₂')
      (IndexedFunctorSquare.base s x₁)
      (IndexedFunctorSquare.tail s x₁))

chain-functor-square-snoc-eq _ _ refl
  = chain-functor-square-snoc

