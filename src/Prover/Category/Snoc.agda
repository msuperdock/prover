module Prover.Category.Snoc where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainDependentFunctorCompose; ChainDependentFunctorIdentity;
    ChainDependentFunctorSquare; ChainFunctor; ChainFunctorCompose;
    ChainFunctorIdentity; ChainFunctorSquare; chain-dependent-category;
    chain-dependent-category₀; chain-dependent-functor;
    chain-dependent-functor₀; chain-dependent-functor-identity;
    chain-dependent-functor-identity₀; chain-dependent-functor-compose;
    chain-dependent-functor-compose₀; chain-dependent-functor-square;
    chain-dependent-functor-square₀; sigma)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedDependentFunctorCompose; IndexedDependentFunctorIdentity;
    IndexedDependentFunctorSquare; IndexedFunctor; IndexedFunctorCompose;
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

-- ### ChainDependentCategory

chain-dependent-category-snoc
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → IndexedDependentCategory C'
  → ChainDependentCategory C (suc n)

-- chain-dependent-functor-snoc
--   : {n : ℕ}
--   → {C : Category}
--   → {C' : Category.Object C → ChainCategory n}
--   → {C'' : (x : Category.Object C) → IndexedCategory (C' x)}
--   → {F : ChainDependentFunctor C C'}
--   → IndexedDependentFunctor C'' F
--   → ChainDependentFunctor C
--     (λ x → chain-category-snoc (C'' x))

-- ### ChainDependentFunctor

chain-dependent-functor-snoc
  : {n : ℕ}
  → {C D : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {C'' : IndexedDependentCategory C'}
  → {D'' : IndexedDependentCategory D'}
  → {F : ChainDependentFunctor C' D'}
  → IndexedDependentFunctor C'' D'' F
  → ChainDependentFunctor
    (chain-dependent-category-snoc C'')
    (chain-dependent-category-snoc D'')

-- ### ChainDependentFunctorIdentity

chain-dependent-functor-identity-snoc
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C'' : IndexedDependentCategory C'}
  → {F : ChainDependentFunctor C' C'}
  → {F' : IndexedDependentFunctor C'' C'' F}
  → IndexedDependentFunctorIdentity F'
  → ChainDependentFunctorIdentity
    (chain-dependent-functor-snoc F')

-- ### ChainDependentFunctorCompose

chain-dependent-functor-compose-snoc
  : {n : ℕ}
  → {C D E : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {E' : ChainDependentCategory E n}
  → {C'' : IndexedDependentCategory C'}
  → {D'' : IndexedDependentCategory D'}
  → {E'' : IndexedDependentCategory E'}
  → {F : ChainDependentFunctor D' E'}
  → {G : ChainDependentFunctor C' D'}
  → {H : ChainDependentFunctor C' E'}
  → {F' : IndexedDependentFunctor D'' E'' F}
  → {G' : IndexedDependentFunctor C'' D'' G}
  → {H' : IndexedDependentFunctor C'' E'' H}
  → IndexedDependentFunctorCompose F' G' H'
  → ChainDependentFunctorCompose
    (chain-dependent-functor-snoc F')
    (chain-dependent-functor-snoc G')
    (chain-dependent-functor-snoc H')

-- ### ChainDependentFunctorSquare

chain-dependent-functor-square-snoc
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : Category}
  → {C₁' : ChainDependentCategory C₁ n}
  → {C₂' : ChainDependentCategory C₂ n}
  → {D₁' : ChainDependentCategory D₁ n}
  → {D₂' : ChainDependentCategory D₂ n}
  → {C₁'' : IndexedDependentCategory C₁'}
  → {C₂'' : IndexedDependentCategory C₂'}
  → {D₁'' : IndexedDependentCategory D₁'}
  → {D₂'' : IndexedDependentCategory D₂'}
  → {F : ChainDependentFunctor C₁' C₂'}
  → {G : ChainDependentFunctor D₁' D₂'}
  → {H₁ : ChainDependentFunctor C₁' D₁'}
  → {H₂ : ChainDependentFunctor C₂' D₂'}
  → {F' : IndexedDependentFunctor C₁'' C₂'' F}
  → {G' : IndexedDependentFunctor D₁'' D₂'' G}
  → {H₁' : IndexedDependentFunctor C₁'' D₁'' H₁}
  → {H₂' : IndexedDependentFunctor C₂'' D₂'' H₂}
  → IndexedDependentFunctorSquare F' G' H₁' H₂'
  → ChainDependentFunctorSquare
    (chain-dependent-functor-snoc F')
    (chain-dependent-functor-snoc G')
    (chain-dependent-functor-snoc H₁')
    (chain-dependent-functor-snoc H₂')

-- ## Definitions

-- ### ChainCategory

chain-category-snoc {n = zero} C
  = sigma
    (chain-dependent-category₀
      (indexed-category₀ C))
chain-category-snoc {n = suc _} C
  = sigma
    (chain-dependent-category-snoc
      (IndexedCategory.unpack C))

-- ### ChainFunctor

chain-functor-snoc {n = zero} F
  = sigma
    (chain-dependent-functor₀
      (indexed-functor₀ F))
chain-functor-snoc {n = suc _} F
  = sigma
    (chain-dependent-functor-snoc
      (IndexedFunctor.unpack F))

-- ### ChainFunctorIdentity

chain-functor-identity-snoc {n = zero} p
  = sigma
    (chain-dependent-functor-identity₀
      (indexed-functor-identity₀ p))
chain-functor-identity-snoc {n = suc _} p
  = sigma
    (chain-dependent-functor-identity-snoc
      (IndexedFunctorIdentity.unpack p))

chain-functor-identity-snoc-eq _ _ refl
  = chain-functor-identity-snoc

-- ### ChainFunctorCompose

chain-functor-compose-snoc {n = zero} p
  = sigma
    (chain-dependent-functor-compose₀
      (indexed-functor-compose₀ p))
chain-functor-compose-snoc {n = suc _} p
  = sigma
    (chain-dependent-functor-compose-snoc
      (IndexedFunctorCompose.unpack p))

chain-functor-compose-snoc-eq _ _ refl
  = chain-functor-compose-snoc

-- ### ChainFunctorSquare

chain-functor-square-snoc {n = zero} s
  = sigma
    (chain-dependent-functor-square₀
      (indexed-functor-square₀ s))
chain-functor-square-snoc {n = suc _} s
  = sigma
    (chain-dependent-functor-square-snoc
      (IndexedFunctorSquare.unpack s))

chain-functor-square-snoc-eq _ _ refl
  = chain-functor-square-snoc

-- ### ChainDependentCategory

chain-dependent-category-snoc C''
  = chain-dependent-category
    (λ x → chain-category-snoc
      (IndexedDependentCategory.indexed-category C'' x))
    (λ f → chain-functor-snoc
      (IndexedDependentCategory.indexed-functor C'' f))
    (λ x → chain-functor-identity-snoc
      (IndexedDependentCategory.indexed-functor-identity C'' x))
    (λ f g → chain-functor-compose-snoc
      (IndexedDependentCategory.indexed-functor-compose C'' f g))

-- ### ChainDependentFunctor

chain-dependent-functor-snoc {F = F} F'
  = chain-dependent-functor
    (ChainDependentFunctor.functor F)
    (λ x → chain-functor-snoc
      (IndexedDependentFunctor.indexed-functor F' x))
    (λ f → chain-functor-square-snoc
      (IndexedDependentFunctor.indexed-functor-square F' f))

-- ### ChainDependentFunctorIdentity

chain-dependent-functor-identity-snoc {C' = C'} {C'' = C''} p
  = chain-dependent-functor-identity
    (IndexedDependentFunctorIdentity.functor p)
    (λ x → chain-functor-identity-snoc-eq
      (ChainDependentCategory.chain-category C')
      (IndexedDependentCategory.indexed-category C'')
      (IndexedDependentFunctorIdentity.base p x)
      (IndexedDependentFunctorIdentity.indexed-functor p x))

-- ### ChainDependentFunctorCompose

chain-dependent-functor-compose-snoc {E' = E'} {E'' = E''} p
  = chain-dependent-functor-compose
    (IndexedDependentFunctorCompose.functor p)
    (λ x → chain-functor-compose-snoc-eq
      (ChainDependentCategory.chain-category E')
      (IndexedDependentCategory.indexed-category E'')
      (IndexedDependentFunctorCompose.base p x)
      (IndexedDependentFunctorCompose.indexed-functor p x))

-- ### ChainDependentFunctorSquare

chain-dependent-functor-square-snoc {D₂' = D₂'} {D₂'' = D₂''} s
  = chain-dependent-functor-square
    (IndexedDependentFunctorSquare.functor s)
    (λ x₁ → chain-functor-square-snoc-eq
      (ChainDependentCategory.chain-category D₂')
      (IndexedDependentCategory.indexed-category D₂'')
      (IndexedDependentFunctorSquare.base s x₁)
      (IndexedDependentFunctorSquare.indexed-functor s x₁))

