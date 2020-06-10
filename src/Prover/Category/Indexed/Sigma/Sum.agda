module Prover.Category.Indexed.Sigma.Sum where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; Functor; FunctorCompose;
    FunctorIdentity; FunctorSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; IndexedDependentFunctor;
    IndexedDependentFunctorCompose; IndexedDependentFunctorIdentity;
    IndexedDependentFunctorSquare; IndexedFunctor; IndexedFunctorCompose;
    IndexedFunctorIdentity; IndexedFunctorSquare; empty; indexed-category₀;
    indexed-dependent-category; indexed-dependent-category₀;
    indexed-dependent-functor; indexed-dependent-functor₀;
    indexed-dependent-functor-compose; indexed-dependent-functor-compose₀;
    indexed-dependent-functor-identity; indexed-dependent-functor-identity₀;
    indexed-dependent-functor-square; indexed-dependent-functor-square₀;
    indexed-functor₀; indexed-functor-compose₀; indexed-functor-identity₀;
    indexed-functor-square₀; sigma)
open import Prover.Category.Indexed.Split
  using (IndexedSplitDependentFunctor; IndexedSplitDependentFunctorSquare;
    IndexedSplitFunctor; IndexedSplitFunctorSquare; indexed-split-functor₀;
    indexed-split-functor-square₀)
open import Prover.Category.Sigma.Sum
  using (category-sigma-sum; functor-compose-sigma-sum;
    functor-identity-sigma-sum; functor-sigma-sum; functor-square-sigma-sum)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-dependent-category-snoc;
    chain-dependent-functor-snoc; chain-functor-snoc)
open import Prover.Category.Split
  using (SplitFunctor; SplitFunctorSquare)
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
  → {C₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → {D₂' : IndexedCategory (chain-category-snoc D₂₁')}
  → {F₁ : IndexedSplitFunctor C₁₁' C₂₁'}
  → {G₁ : IndexedSplitFunctor D₁₁' D₂₁'}
  → {H : ChainFunctor C D}
  → {H₁₁' : IndexedFunctor C₁₁' D₁₁' H}
  → {H₂₁' : IndexedFunctor C₂₁' D₂₁' H}
  → IndexedFunctor C₂' D₂' (chain-functor-snoc H₂₁')
  → IndexedSplitFunctorSquare H₁₁' H₂₁' F₁ G₁
  → IndexedFunctor
    (indexed-category-sigma-sum C₂' F₁)
    (indexed-category-sigma-sum D₂' G₁) H

-- ### IndexedFunctorIdentity

indexed-functor-identity-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {C₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → {F₁ : IndexedSplitFunctor C₁₁' C₂₁'}
  → {G : ChainFunctor C C}
  → {G₁₁' : IndexedFunctor C₁₁' C₁₁' G}
  → {G₂₁' : IndexedFunctor C₂₁' C₂₁' G}
  → {G₂' : IndexedFunctor C₂' C₂' (chain-functor-snoc G₂₁')}
  → (s₁ : IndexedSplitFunctorSquare G₁₁' G₂₁' F₁ F₁)
  → IndexedFunctorIdentity G₁₁'
  → IndexedFunctorIdentity G₂'
  → IndexedFunctorIdentity
    (indexed-functor-sigma-sum G₂' s₁)

indexed-functor-identity-sigma-sum-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁₁' C₂₁' : (x : A) → IndexedCategory (C x))
  → (C₂' : (x : A) → IndexedCategory (chain-category-snoc (C₂₁' x)))
  → (F₁ : (x : A) → IndexedSplitFunctor (C₁₁' x) (C₂₁' x))
  → {G : ChainFunctor (C x₁) (C x₂)}
  → {G₁₁' : IndexedFunctor (C₁₁' x₁) (C₁₁' x₂) G}
  → {G₂₁' : IndexedFunctor (C₂₁' x₁) (C₂₁' x₂) G}
  → {G₂' : IndexedFunctor (C₂' x₁) (C₂' x₂) (chain-functor-snoc G₂₁')}
  → (s₁ : IndexedSplitFunctorSquare G₁₁' G₂₁' (F₁ x₁) (F₁ x₂))
  → x₂ ≡ x₁
  → IndexedFunctorIdentity G₁₁'
  → IndexedFunctorIdentity G₂'
  → IndexedFunctorIdentity
    (indexed-functor-sigma-sum G₂' s₁)

-- ### IndexedFunctorCompose

indexed-functor-compose-sigma-sum
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {D₁₁' D₂₁' : IndexedCategory D}
  → {E₁₁' E₂₁' : IndexedCategory E}
  → {C₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → {D₂' : IndexedCategory (chain-category-snoc D₂₁')}
  → {E₂' : IndexedCategory (chain-category-snoc E₂₁')}
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
  → {I₂' : IndexedFunctor D₂' E₂' (chain-functor-snoc I₂₁')}
  → {J₂' : IndexedFunctor C₂' D₂' (chain-functor-snoc J₂₁')}
  → {K₂' : IndexedFunctor C₂' E₂' (chain-functor-snoc K₂₁')}
  → (s₁ : IndexedSplitFunctorSquare I₁₁' I₂₁' G₁ H₁)
  → (t₁ : IndexedSplitFunctorSquare J₁₁' J₂₁' F₁ G₁)
  → (u₁ : IndexedSplitFunctorSquare K₁₁' K₂₁' F₁ H₁)
  → IndexedFunctorCompose I₁₁' J₁₁' K₁₁'
  → IndexedFunctorCompose I₂' J₂' K₂'
  → IndexedFunctorCompose
    (indexed-functor-sigma-sum I₂' s₁)
    (indexed-functor-sigma-sum J₂' t₁)
    (indexed-functor-sigma-sum K₂' u₁)

indexed-functor-compose-sigma-sum-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C₁₁' C₂₁' : IndexedCategory C}
  → {D₁₁' D₂₁' : IndexedCategory D}
  → (E₁₁' E₂₁' : (x : A) → IndexedCategory (E x))
  → {C₂' : IndexedCategory (chain-category-snoc C₂₁')}
  → {D₂' : IndexedCategory (chain-category-snoc D₂₁')}
  → (E₂' : (x : A) → IndexedCategory (chain-category-snoc (E₂₁' x)))
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
  → {I₂' : IndexedFunctor D₂' (E₂' x₁) (chain-functor-snoc I₂₁')}
  → {J₂' : IndexedFunctor C₂' D₂' (chain-functor-snoc J₂₁')}
  → {K₂' : IndexedFunctor C₂' (E₂' x₂) (chain-functor-snoc K₂₁')}
  → (s₁ : IndexedSplitFunctorSquare I₁₁' I₂₁' G₁ (H₁ x₁))
  → (t₁ : IndexedSplitFunctorSquare J₁₁' J₂₁' F₁ G₁)
  → (u₁ : IndexedSplitFunctorSquare K₁₁' K₂₁' F₁ (H₁ x₂))
  → x₂ ≡ x₁
  → IndexedFunctorCompose I₁₁' J₁₁' K₁₁'
  → IndexedFunctorCompose I₂' J₂' K₂'
  → IndexedFunctorCompose
    (indexed-functor-sigma-sum I₂' s₁)
    (indexed-functor-sigma-sum J₂' t₁)
    (indexed-functor-sigma-sum K₂' u₁)

-- ### IndexedFunctorSquare

indexed-functor-square-sigma-sum
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁₁₁' C₁₂₁' : IndexedCategory C₁}
  → {C₂₁₁' C₂₂₁' : IndexedCategory C₂}
  → {D₁₁₁' D₁₂₁' : IndexedCategory D₁}
  → {D₂₁₁' D₂₂₁' : IndexedCategory D₂}
  → {C₁₂' : IndexedCategory (chain-category-snoc C₁₂₁')}
  → {C₂₂' : IndexedCategory (chain-category-snoc C₂₂₁')}
  → {D₁₂' : IndexedCategory (chain-category-snoc D₁₂₁')}
  → {D₂₂' : IndexedCategory (chain-category-snoc D₂₂₁')}
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
  → {H₂' : IndexedFunctor C₁₂' C₂₂' (chain-functor-snoc H₂₁')}
  → {I₂' : IndexedFunctor D₁₂' D₂₂' (chain-functor-snoc I₂₁')}
  → {J₁₂' : IndexedFunctor C₁₂' D₁₂' (chain-functor-snoc J₁₂₁')}
  → {J₂₂' : IndexedFunctor C₂₂' D₂₂' (chain-functor-snoc J₂₂₁')}
  → (s₁ : IndexedSplitFunctorSquare H₁₁' H₂₁' F₁₁ F₂₁)
  → (t₁ : IndexedSplitFunctorSquare I₁₁' I₂₁' G₁₁ G₂₁)
  → (u₁₁ : IndexedSplitFunctorSquare J₁₁₁' J₁₂₁' F₁₁ G₁₁)
  → (u₂₁ : IndexedSplitFunctorSquare J₂₁₁' J₂₂₁' F₂₁ G₂₁)
  → IndexedFunctorSquare H₁₁' I₁₁' J₁₁₁' J₂₁₁'
  → IndexedFunctorSquare H₂' I₂' J₁₂' J₂₂'
  → IndexedFunctorSquare
    (indexed-functor-sigma-sum H₂' s₁)
    (indexed-functor-sigma-sum I₂' t₁)
    (indexed-functor-sigma-sum J₁₂' u₁₁)
    (indexed-functor-sigma-sum J₂₂' u₂₁)

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
  → {C₁₂' : IndexedCategory (chain-category-snoc C₁₂₁')}
  → {C₂₂' : IndexedCategory (chain-category-snoc C₂₂₁')}
  → {D₁₂' : IndexedCategory (chain-category-snoc D₁₂₁')}
  → (D₂₂' : (x : A) → IndexedCategory (chain-category-snoc (D₂₂₁' x)))
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
  → {H₂' : IndexedFunctor C₁₂' C₂₂' (chain-functor-snoc H₂₁')}
  → {I₂' : IndexedFunctor D₁₂' (D₂₂' x₁) (chain-functor-snoc I₂₁')}
  → {J₁₂' : IndexedFunctor C₁₂' D₁₂' (chain-functor-snoc J₁₂₁')}
  → {J₂₂' : IndexedFunctor C₂₂' (D₂₂' x₂) (chain-functor-snoc J₂₂₁')}
  → (s₁ : IndexedSplitFunctorSquare H₁₁' H₂₁' F₁₁ F₂₁)
  → (t₁ : IndexedSplitFunctorSquare I₁₁' I₂₁' G₁₁ (G₂₁ x₁))
  → (u₁₁ : IndexedSplitFunctorSquare J₁₁₁' J₁₂₁' F₁₁ G₁₁)
  → (u₂₁ : IndexedSplitFunctorSquare J₂₁₁' J₂₂₁' F₂₁ (G₂₁ x₂))
  → x₂ ≡ x₁
  → IndexedFunctorSquare H₁₁' I₁₁' J₁₁₁' J₂₁₁'
  → IndexedFunctorSquare H₂' I₂' J₁₂' J₂₂'
  → IndexedFunctorSquare
    (indexed-functor-sigma-sum H₂' s₁)
    (indexed-functor-sigma-sum I₂' t₁)
    (indexed-functor-sigma-sum J₁₂' u₁₁)
    (indexed-functor-sigma-sum J₂₂' u₂₁)

-- ### IndexedDependentCategory

indexed-dependent-category-sigma-sum
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C₁₁'' C₂₁'' : IndexedDependentCategory C'}
  → (C₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₂₁''))
  → IndexedSplitDependentFunctor C₁₁'' C₂₁''
  → IndexedDependentCategory C'

-- ### IndexedDependentFunctor

indexed-dependent-functor-sigma-sum
  : {n : ℕ}
  → {C D : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {C₁₁'' C₂₁'' : IndexedDependentCategory C'}
  → {D₁₁'' D₂₁'' : IndexedDependentCategory D'}
  → {C₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₂₁'')}
  → {D₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₂₁'')}
  → {F₁ : IndexedSplitDependentFunctor C₁₁'' C₂₁''}
  → {G₁ : IndexedSplitDependentFunctor D₁₁'' D₂₁''}
  → {H : ChainDependentFunctor C' D'}
  → {H₁₁' : IndexedDependentFunctor C₁₁'' D₁₁'' H}
  → {H₂₁' : IndexedDependentFunctor C₂₁'' D₂₁'' H}
  → IndexedDependentFunctor C₂'' D₂''
    (chain-dependent-functor-snoc H₂₁')
  → IndexedSplitDependentFunctorSquare H₁₁' H₂₁' F₁ G₁
  → IndexedDependentFunctor
    (indexed-dependent-category-sigma-sum C₂'' F₁)
    (indexed-dependent-category-sigma-sum D₂'' G₁) H

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-sigma-sum
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → {C₁₁'' C₂₁'' : IndexedDependentCategory C'}
  → {C₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₂₁'')}
  → {F₁ : IndexedSplitDependentFunctor C₁₁'' C₂₁''}
  → {G : ChainDependentFunctor C' C'}
  → {G₁₁' : IndexedDependentFunctor C₁₁'' C₁₁'' G}
  → {G₂₁' : IndexedDependentFunctor C₂₁'' C₂₁'' G}
  → {G₂' : IndexedDependentFunctor C₂'' C₂''
    (chain-dependent-functor-snoc G₂₁')}
  → (s₁ : IndexedSplitDependentFunctorSquare G₁₁' G₂₁' F₁ F₁)
  → IndexedDependentFunctorIdentity G₁₁'
  → IndexedDependentFunctorIdentity G₂'
  → IndexedDependentFunctorIdentity
    (indexed-dependent-functor-sigma-sum G₂' s₁)

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-sigma-sum
  : {n : ℕ}
  → {C D E : Category}
  → {C' : ChainDependentCategory C n}
  → {D' : ChainDependentCategory D n}
  → {E' : ChainDependentCategory E n}
  → {C₁₁'' C₂₁'' : IndexedDependentCategory C'}
  → {D₁₁'' D₂₁'' : IndexedDependentCategory D'}
  → {E₁₁'' E₂₁'' : IndexedDependentCategory E'}
  → {C₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₂₁'')}
  → {D₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₂₁'')}
  → {E₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc E₂₁'')}
  → {F₁ : IndexedSplitDependentFunctor C₁₁'' C₂₁''}
  → {G₁ : IndexedSplitDependentFunctor D₁₁'' D₂₁''}
  → {H₁ : IndexedSplitDependentFunctor E₁₁'' E₂₁''}
  → {I : ChainDependentFunctor D' E'}
  → {J : ChainDependentFunctor C' D'}
  → {K : ChainDependentFunctor C' E'}
  → {I₁₁' : IndexedDependentFunctor D₁₁'' E₁₁'' I}
  → {I₂₁' : IndexedDependentFunctor D₂₁'' E₂₁'' I}
  → {J₁₁' : IndexedDependentFunctor C₁₁'' D₁₁'' J}
  → {J₂₁' : IndexedDependentFunctor C₂₁'' D₂₁'' J}
  → {K₁₁' : IndexedDependentFunctor C₁₁'' E₁₁'' K}
  → {K₂₁' : IndexedDependentFunctor C₂₁'' E₂₁'' K}
  → {I₂' : IndexedDependentFunctor D₂'' E₂''
    (chain-dependent-functor-snoc I₂₁')}
  → {J₂' : IndexedDependentFunctor C₂'' D₂''
    (chain-dependent-functor-snoc J₂₁')}
  → {K₂' : IndexedDependentFunctor C₂'' E₂''
    (chain-dependent-functor-snoc K₂₁')}
  → (s₁ : IndexedSplitDependentFunctorSquare I₁₁' I₂₁' G₁ H₁)
  → (t₁ : IndexedSplitDependentFunctorSquare J₁₁' J₂₁' F₁ G₁)
  → (u₁ : IndexedSplitDependentFunctorSquare K₁₁' K₂₁' F₁ H₁)
  → IndexedDependentFunctorCompose I₁₁' J₁₁' K₁₁'
  → IndexedDependentFunctorCompose I₂' J₂' K₂'
  → IndexedDependentFunctorCompose
    (indexed-dependent-functor-sigma-sum I₂' s₁)
    (indexed-dependent-functor-sigma-sum J₂' t₁)
    (indexed-dependent-functor-sigma-sum K₂' u₁)

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-sigma-sum
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : Category}
  → {C₁' : ChainDependentCategory C₁ n}
  → {C₂' : ChainDependentCategory C₂ n}
  → {D₁' : ChainDependentCategory D₁ n}
  → {D₂' : ChainDependentCategory D₂ n}
  → {C₁₁₁'' C₁₂₁'' : IndexedDependentCategory C₁'}
  → {C₂₁₁'' C₂₂₁'' : IndexedDependentCategory C₂'}
  → {D₁₁₁'' D₁₂₁'' : IndexedDependentCategory D₁'}
  → {D₂₁₁'' D₂₂₁'' : IndexedDependentCategory D₂'}
  → {C₁₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₁₂₁'')}
  → {C₂₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc C₂₂₁'')}
  → {D₁₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₁₂₁'')}
  → {D₂₂'' : IndexedDependentCategory
    (chain-dependent-category-snoc D₂₂₁'')}
  → {F₁₁ : IndexedSplitDependentFunctor C₁₁₁'' C₁₂₁''}
  → {F₂₁ : IndexedSplitDependentFunctor C₂₁₁'' C₂₂₁''}
  → {G₁₁ : IndexedSplitDependentFunctor D₁₁₁'' D₁₂₁''}
  → {G₂₁ : IndexedSplitDependentFunctor D₂₁₁'' D₂₂₁''}
  → {H : ChainDependentFunctor C₁' C₂'}
  → {I : ChainDependentFunctor D₁' D₂'}
  → {J₁ : ChainDependentFunctor C₁' D₁'}
  → {J₂ : ChainDependentFunctor C₂' D₂'}
  → {H₁₁' : IndexedDependentFunctor C₁₁₁'' C₂₁₁'' H}
  → {H₂₁' : IndexedDependentFunctor C₁₂₁'' C₂₂₁'' H}
  → {I₁₁' : IndexedDependentFunctor D₁₁₁'' D₂₁₁'' I}
  → {I₂₁' : IndexedDependentFunctor D₁₂₁'' D₂₂₁'' I}
  → {J₁₁₁' : IndexedDependentFunctor C₁₁₁'' D₁₁₁'' J₁}
  → {J₁₂₁' : IndexedDependentFunctor C₁₂₁'' D₁₂₁'' J₁}
  → {J₂₁₁' : IndexedDependentFunctor C₂₁₁'' D₂₁₁'' J₂}
  → {J₂₂₁' : IndexedDependentFunctor C₂₂₁'' D₂₂₁'' J₂}
  → {H₂' : IndexedDependentFunctor C₁₂'' C₂₂''
    (chain-dependent-functor-snoc H₂₁')}
  → {I₂' : IndexedDependentFunctor D₁₂'' D₂₂''
    (chain-dependent-functor-snoc I₂₁')}
  → {J₁₂' : IndexedDependentFunctor C₁₂'' D₁₂''
    (chain-dependent-functor-snoc J₁₂₁')}
  → {J₂₂' : IndexedDependentFunctor C₂₂'' D₂₂''
    (chain-dependent-functor-snoc J₂₂₁')}
  → (s₁ : IndexedSplitDependentFunctorSquare H₁₁' H₂₁' F₁₁ F₂₁)
  → (t₁ : IndexedSplitDependentFunctorSquare I₁₁' I₂₁' G₁₁ G₂₁)
  → (u₁₁ : IndexedSplitDependentFunctorSquare J₁₁₁' J₁₂₁' F₁₁ G₁₁)
  → (u₂₁ : IndexedSplitDependentFunctorSquare J₂₁₁' J₂₂₁' F₂₁ G₂₁)
  → IndexedDependentFunctorSquare H₁₁' I₁₁' J₁₁₁' J₂₁₁'
  → IndexedDependentFunctorSquare H₂' I₂' J₁₂' J₂₂'
  → IndexedDependentFunctorSquare
    (indexed-dependent-functor-sigma-sum H₂' s₁)
    (indexed-dependent-functor-sigma-sum I₂' t₁)
    (indexed-dependent-functor-sigma-sum J₁₂' u₁₁)
    (indexed-dependent-functor-sigma-sum J₂₂' u₂₁)

-- ## Definitions

-- ### IndexedCategory

indexed-category-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'} C₂' F₁
  = empty
    (category-sigma-sum
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      (indexed-dependent-category₀
        (IndexedCategory.unpack C₂'))
      (indexed-split-functor₀ F₁))
indexed-category-sigma-sum
  {n = suc _} C₂' F₁
  = sigma
    (indexed-dependent-category-sigma-sum
      (IndexedCategory.unpack C₂')
      (IndexedSplitFunctor.unpack F₁))

-- ### IndexedFunctor

indexed-functor-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {D₁₁' = D₁₁'} {D₂₁' = D₂₁'}
  {C₂' = C₂'} {D₂' = D₂'}
  {F₁ = F₁} {G₁ = G₁}
  {H₁₁' = H₁₁'} H₂' s₁
  = empty
    (functor-sigma-sum
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {C₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂')}
      {D₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₂')}
      {F₁ = indexed-split-functor₀ F₁}
      {G₁ = indexed-split-functor₀ G₁}
      {H₁₁ = indexed-functor₀ H₁₁'}
      (indexed-dependent-functor₀
        (IndexedFunctor.unpack H₂'))
      (indexed-split-functor-square₀ s₁))
indexed-functor-sigma-sum
  {n = suc _} H₂' s₁
  = sigma
    (indexed-dependent-functor-sigma-sum
      (IndexedFunctor.unpack H₂')
      (IndexedSplitFunctorSquare.unpack s₁))

-- ### IndexedFunctorIdentity

indexed-functor-identity-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {C₂' = C₂'}
  {F₁ = F₁}
  {G₁₁' = G₁₁'}
  {G₂' = G₂'} s₁ p₁₁ p₂
  = empty
    (functor-identity-sigma-sum
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {C₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂')}
      {F₁ = indexed-split-functor₀ F₁}
      {G₁₁ = indexed-functor₀ G₁₁'}
      {G₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack G₂')}
      (indexed-split-functor-square₀ s₁)
      (indexed-functor-identity₀ p₁₁)
      (indexed-dependent-functor-identity₀
        (IndexedFunctorIdentity.unpack p₂)))
indexed-functor-identity-sigma-sum
  {n = suc _} s₁ p₁₁ p₂
  = sigma
    (indexed-dependent-functor-identity-sigma-sum
      (IndexedSplitFunctorSquare.unpack s₁)
      (IndexedFunctorIdentity.unpack p₁₁)
      (IndexedFunctorIdentity.unpack p₂))

indexed-functor-identity-sigma-sum-eq _ _ _ _ _ s₁ refl
  = indexed-functor-identity-sigma-sum s₁

-- ### IndexedFunctorCompose

indexed-functor-compose-sigma-sum
  {n = zero}
  {C₁₁' = C₁₁'} {C₂₁' = C₂₁'}
  {D₁₁' = D₁₁'} {D₂₁' = D₂₁'}
  {E₁₁' = E₁₁'} {E₂₁' = E₂₁'} 
  {C₂' = C₂'} {D₂' = D₂'} {E₂' = E₂'}
  {F₁ = F₁} {G₁ = G₁} {H₁ = H₁}
  {I₁₁' = I₁₁'} {J₁₁' = J₁₁'} {K₁₁' = K₁₁'}
  {I₂' = I₂'} {J₂' = J₂'} {K₂' = K₂'} s₁ t₁ u₁ p₁₁ p₂
  = empty
    (functor-compose-sigma-sum
      {C₁₁ = indexed-category₀ C₁₁'}
      {C₂₁ = indexed-category₀ C₂₁'}
      {D₁₁ = indexed-category₀ D₁₁'}
      {D₂₁ = indexed-category₀ D₂₁'}
      {E₁₁ = indexed-category₀ E₁₁'}
      {E₂₁ = indexed-category₀ E₂₁'}
      {C₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂')}
      {D₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₂')}
      {E₂ = indexed-dependent-category₀
        (IndexedCategory.unpack E₂')}
      {I₁ = indexed-split-functor₀ F₁}
      {J₁ = indexed-split-functor₀ G₁}
      {K₁ = indexed-split-functor₀ H₁}
      {L₁₁ = indexed-functor₀ I₁₁'}
      {M₁₁ = indexed-functor₀ J₁₁'}
      {N₁₁ = indexed-functor₀ K₁₁'}
      {L₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack I₂')}
      {M₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack J₂')}
      {N₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack K₂')}
      (indexed-split-functor-square₀ s₁)
      (indexed-split-functor-square₀ t₁)
      (indexed-split-functor-square₀ u₁)
      (indexed-functor-compose₀ p₁₁)
      (indexed-dependent-functor-compose₀
        (IndexedFunctorCompose.unpack p₂)))
indexed-functor-compose-sigma-sum
  {n = suc _} s₁ t₁ u₁ p₁₁ p₂
  = sigma
    (indexed-dependent-functor-compose-sigma-sum
      (IndexedSplitFunctorSquare.unpack s₁)
      (IndexedSplitFunctorSquare.unpack t₁)
      (IndexedSplitFunctorSquare.unpack u₁)
      (IndexedFunctorCompose.unpack p₁₁)
      (IndexedFunctorCompose.unpack p₂))

indexed-functor-compose-sigma-sum-eq _ _ _ _ _ s₁ t₁ u₁ refl
  = indexed-functor-compose-sigma-sum s₁ t₁ u₁

-- ### IndexedFunctorSquare

indexed-functor-square-sigma-sum
  {n = zero}
  {C₁₁₁' = C₁₁₁'} {C₁₂₁' = C₁₂₁'}
  {C₂₁₁' = C₂₁₁'} {C₂₂₁' = C₂₂₁'}
  {D₁₁₁' = D₁₁₁'} {D₁₂₁' = D₁₂₁'}
  {D₂₁₁' = D₂₁₁'} {D₂₂₁' = D₂₂₁'}
  {C₁₂' = C₁₂'} {C₂₂' = C₂₂'} {D₁₂' = D₁₂'} {D₂₂' = D₂₂'}
  {F₁₁ = F₁₁} {F₂₁ = F₂₁} {G₁₁ = G₁₁} {G₂₁ = G₂₁}
  {H₁₁' = H₁₁'} {I₁₁' = I₁₁'} {J₁₁₁' = J₁₁₁'} {J₂₁₁' = J₂₁₁'}
  {H₂' = H₂'} {I₂' = I₂'} {J₁₂' = J₁₂'} {J₂₂' = J₂₂'}
  s₁ t₁ u₁₁ u₂₁ s₁₁ s₂
  = empty
    (functor-square-sigma-sum
      {C₁₁₁ = indexed-category₀ C₁₁₁'}
      {C₁₂₁ = indexed-category₀ C₁₂₁'}
      {C₂₁₁ = indexed-category₀ C₂₁₁'}
      {C₂₂₁ = indexed-category₀ C₂₂₁'}
      {D₁₁₁ = indexed-category₀ D₁₁₁'}
      {D₁₂₁ = indexed-category₀ D₁₂₁'}
      {D₂₁₁ = indexed-category₀ D₂₁₁'}
      {D₂₂₁ = indexed-category₀ D₂₂₁'}
      {C₁₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₁₂')}
      {C₂₂ = indexed-dependent-category₀
        (IndexedCategory.unpack C₂₂')}
      {D₁₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₁₂')}
      {D₂₂ = indexed-dependent-category₀
        (IndexedCategory.unpack D₂₂')}
      {F₁₁ = indexed-split-functor₀ F₁₁}
      {F₂₁ = indexed-split-functor₀ F₂₁}
      {G₁₁ = indexed-split-functor₀ G₁₁}
      {G₂₁ = indexed-split-functor₀ G₂₁}
      {H₁₁ = indexed-functor₀ H₁₁'}
      {I₁₁ = indexed-functor₀ I₁₁'}
      {J₁₁₁ = indexed-functor₀ J₁₁₁'}
      {J₂₁₁ = indexed-functor₀ J₂₁₁'}
      {H₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack H₂')}
      {I₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack I₂')}
      {J₁₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack J₁₂')}
      {J₂₂ = indexed-dependent-functor₀
        (IndexedFunctor.unpack J₂₂')}
      (indexed-split-functor-square₀ s₁)
      (indexed-split-functor-square₀ t₁)
      (indexed-split-functor-square₀ u₁₁)
      (indexed-split-functor-square₀ u₂₁)
      (indexed-functor-square₀ s₁₁)
      (indexed-dependent-functor-square₀
        (IndexedFunctorSquare.unpack s₂)))
indexed-functor-square-sigma-sum
  {n = suc _} s₁ t₁ u₁₁ u₂₁ s₁₁ s₂
  = sigma
    (indexed-dependent-functor-square-sigma-sum
      (IndexedSplitFunctorSquare.unpack s₁)
      (IndexedSplitFunctorSquare.unpack t₁)
      (IndexedSplitFunctorSquare.unpack u₁₁)
      (IndexedSplitFunctorSquare.unpack u₂₁)
      (IndexedFunctorSquare.unpack s₁₁)
      (IndexedFunctorSquare.unpack s₂))

indexed-functor-square-sigma-sum-eq _ _ _ _ _ s₁ t₁ u₁₁ u₂₁ refl
  = indexed-functor-square-sigma-sum s₁ t₁ u₁₁ u₂₁

-- ### IndexedDependentCategory

indexed-dependent-category-sigma-sum
  {C = C} {C₁₁'' = C₁₁''}
  C₂'' F₁
  = indexed-dependent-category
    (λ x → indexed-category-sigma-sum
      (IndexedDependentCategory.indexed-category C₂'' x)
      (IndexedSplitDependentFunctor.indexed-split-functor F₁ x))
    (λ f → indexed-functor-sigma-sum
      (IndexedDependentCategory.indexed-functor C₂'' f)
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₁ f))
    (λ x → indexed-functor-identity-sigma-sum
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₁
        (Category.identity C x))
      (IndexedDependentCategory.indexed-functor-identity C₁₁'' x)
      (IndexedDependentCategory.indexed-functor-identity C₂'' x))
    (λ f g → indexed-functor-compose-sigma-sum
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₁ f)
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₁ g)
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₁
        (Category.compose C f g))
      (IndexedDependentCategory.indexed-functor-compose C₁₁'' f g)
      (IndexedDependentCategory.indexed-functor-compose C₂'' f g))

-- ### IndexedDependentFunctor

indexed-dependent-functor-sigma-sum
  {F₁ = F₁} {G₁ = G₁} {H = H} {H₁₁' = H₁₁'}
  H₂' s₁
  = indexed-dependent-functor
    (λ x → indexed-functor-sigma-sum
      (IndexedDependentFunctor.indexed-functor H₂' x)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₁ x))
    (λ {x = x} {y = y} f → indexed-functor-square-sigma-sum
      (IndexedSplitDependentFunctor.indexed-split-functor-square F₁ f)
      (IndexedSplitDependentFunctor.indexed-split-functor-square G₁
        (ChainDependentFunctor.map H f))
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₁ x)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₁ y)
      (IndexedDependentFunctor.indexed-functor-square H₁₁' f)
      (IndexedDependentFunctor.indexed-functor-square H₂' f))

-- ### IndexedDependentFunctorIdentity

indexed-dependent-functor-identity-sigma-sum
  {C' = C'} {C₁₁'' = C₁₁''} {C₂₁'' = C₂₁''} {C₂'' = C₂''} {F₁ = F₁}
  s₁ p₁₁ p₂
  = indexed-dependent-functor-identity
    (IndexedDependentFunctorIdentity.functor p₁₁)
    (λ x → indexed-functor-identity-sigma-sum-eq
      (ChainDependentCategory.chain-category C')
      (IndexedDependentCategory.indexed-category C₁₁'')
      (IndexedDependentCategory.indexed-category C₂₁'')
      (IndexedDependentCategory.indexed-category C₂'')
      (IndexedSplitDependentFunctor.indexed-split-functor F₁)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₁ x)
      (IndexedDependentFunctorIdentity.base p₁₁ x)
      (IndexedDependentFunctorIdentity.indexed-functor p₁₁ x)
      (IndexedDependentFunctorIdentity.indexed-functor p₂ x))

-- ### IndexedDependentFunctorCompose

indexed-dependent-functor-compose-sigma-sum
  {E' = E'} {E₁₁'' = E₁₁''} {E₂₁'' = E₂₁''} {E₂'' = E₂''} {H₁ = H₁} {J = J}
  s₁ t₁ u₁ p₁₁ p₂
  = indexed-dependent-functor-compose
    (IndexedDependentFunctorCompose.functor p₁₁)
    (λ x → indexed-functor-compose-sigma-sum-eq
      (ChainDependentCategory.chain-category E')
      (IndexedDependentCategory.indexed-category E₁₁'')
      (IndexedDependentCategory.indexed-category E₂₁'')
      (IndexedDependentCategory.indexed-category E₂'')
      (IndexedSplitDependentFunctor.indexed-split-functor H₁)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₁
        (ChainDependentFunctor.base J x))
      (IndexedSplitDependentFunctorSquare.indexed-split-functor t₁ x)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor u₁ x)
      (IndexedDependentFunctorCompose.base p₁₁ x)
      (IndexedDependentFunctorCompose.indexed-functor p₁₁ x)
      (IndexedDependentFunctorCompose.indexed-functor p₂ x))

-- ### IndexedDependentFunctorSquare

indexed-dependent-functor-square-sigma-sum
  {D₂' = D₂'} {D₂₁₁'' = D₂₁₁''} {D₂₂₁'' = D₂₂₁''} {D₂₂'' = D₂₂''} {G₂₁ = G₂₁}
  {H = H} {J₁ = J₁}
  s₁ t₁ u₁₁ u₂₁ v₁₁ v₂
  = indexed-dependent-functor-square
    (IndexedDependentFunctorSquare.functor v₁₁)
    (λ x₁ → indexed-functor-square-sigma-sum-eq
      (ChainDependentCategory.chain-category D₂')
      (IndexedDependentCategory.indexed-category D₂₁₁'')
      (IndexedDependentCategory.indexed-category D₂₂₁'')
      (IndexedDependentCategory.indexed-category D₂₂'')
      (IndexedSplitDependentFunctor.indexed-split-functor G₂₁)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor s₁ x₁)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor t₁
        (ChainDependentFunctor.base J₁ x₁))
      (IndexedSplitDependentFunctorSquare.indexed-split-functor u₁₁ x₁)
      (IndexedSplitDependentFunctorSquare.indexed-split-functor u₂₁
        (ChainDependentFunctor.base H x₁))
      (IndexedDependentFunctorSquare.base v₁₁ x₁)
      (IndexedDependentFunctorSquare.indexed-functor v₁₁ x₁)
      (IndexedDependentFunctorSquare.indexed-functor v₂ x₁))

