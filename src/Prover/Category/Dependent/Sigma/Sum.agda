module Prover.Category.Dependent.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorEqual;
    ChainFunctorIdentity; ChainFunctorSquare)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorEqual; DependentFunctorIdentity; DependentFunctorSquare)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; DependentSplitFunctorSquare)
open import Prover.Category.Sigma.Sum
  using (category-sigma-sum; functor-compose-sigma-sum; functor-equal-sigma-sum;
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

-- ### DependentFunctorEqual

dependent-functor-equal-sigma-sum
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {D₁₁' D₂₁' : DependentCategory D}
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → {D₂₂' : DependentCategory (chain-category-snoc D₂₁')}
  → {F₁ : DependentSplitFunctor C₁₁' C₂₁'}
  → {G₁ : DependentSplitFunctor D₁₁' D₂₁'}
  → {H₁ H₂ : ChainFunctor C D}
  → {H₁₁₁' : DependentFunctor C₁₁' D₁₁' H₁}
  → {H₁₁₂' : DependentFunctor C₁₁' D₁₁' H₂}
  → {H₂₁₁' : DependentFunctor C₂₁' D₂₁' H₁}
  → {H₂₁₂' : DependentFunctor C₂₁' D₂₁' H₂}
  → {H₂₂₁' : DependentFunctor C₂₂' D₂₂' (chain-functor-snoc H₂₁₁')}
  → {H₂₂₂' : DependentFunctor C₂₂' D₂₂' (chain-functor-snoc H₂₁₂')}
  → (s₁₁ : DependentSplitFunctorSquare H₁₁₁' H₂₁₁' F₁ G₁)
  → (s₁₂ : DependentSplitFunctorSquare H₁₁₂' H₂₁₂' F₁ G₁)
  → ChainFunctorEqual H₁ H₂
  → DependentFunctorEqual H₁₁₁' H₁₁₂'
  → DependentFunctorEqual H₂₁₁' H₂₁₂'
  → DependentFunctorEqual H₂₂₁' H₂₂₂'
  → DependentFunctorEqual
    (dependent-functor-sigma-sum H₂₂₁' s₁₁)
    (dependent-functor-sigma-sum H₂₂₂' s₁₂)

dependent-functor-equal-sigma-sum'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C : ChainCategory n}
  → (D : A → ChainCategory n)
  → {C₁₁' C₂₁' : DependentCategory C}
  → (D₁₁' D₂₁' : (x : A) → DependentCategory (D x))
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → (D₂₂' : (x : A) → DependentCategory (chain-category-snoc (D₂₁' x)))
  → {F₁ : DependentSplitFunctor C₁₁' C₂₁'}
  → (G₁ : (x : A) → DependentSplitFunctor (D₁₁' x) (D₂₁' x))
  → {H₁ : ChainFunctor C (D x₁)}
  → {H₂ : ChainFunctor C (D x₂)}
  → {H₁₁₁' : DependentFunctor C₁₁' (D₁₁' x₁) H₁}
  → {H₁₁₂' : DependentFunctor C₁₁' (D₁₁' x₂) H₂}
  → {H₂₁₁' : DependentFunctor C₂₁' (D₂₁' x₁) H₁}
  → {H₂₁₂' : DependentFunctor C₂₁' (D₂₁' x₂) H₂}
  → {H₂₂₁' : DependentFunctor C₂₂' (D₂₂' x₁) (chain-functor-snoc H₂₁₁')}
  → {H₂₂₂' : DependentFunctor C₂₂' (D₂₂' x₂) (chain-functor-snoc H₂₁₂')}
  → (s₁₁ : DependentSplitFunctorSquare H₁₁₁' H₂₁₁' F₁ (G₁ x₁))
  → (s₁₂ : DependentSplitFunctorSquare H₁₁₂' H₂₁₂' F₁ (G₁ x₂))
  → x₁ ≡ x₂
  → ChainFunctorEqual H₁ H₂
  → DependentFunctorEqual H₁₁₁' H₁₁₂'
  → DependentFunctorEqual H₂₁₁' H₂₁₂'
  → DependentFunctorEqual H₂₂₁' H₂₂₂'
  → DependentFunctorEqual
    (dependent-functor-sigma-sum H₂₂₁' s₁₁)
    (dependent-functor-sigma-sum H₂₂₂' s₁₂)

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
  → ChainFunctorIdentity G
  → DependentFunctorIdentity G₁₁'
  → DependentFunctorIdentity G₂₁'
  → DependentFunctorIdentity G₂₂'
  → DependentFunctorIdentity
    (dependent-functor-sigma-sum G₂₂' s₁)

dependent-functor-identity-sigma-sum'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C₁₁' C₂₁' : (x : A) → DependentCategory (C x))
  → (C₂₂' : (x : A) → DependentCategory (chain-category-snoc (C₂₁' x)))
  → (F₁ : (x : A) → DependentSplitFunctor (C₁₁' x) (C₂₁' x))
  → {G : ChainFunctor (C x₂) (C x₁)}
  → {G₁₁' : DependentFunctor (C₁₁' x₂) (C₁₁' x₁) G}
  → {G₂₁' : DependentFunctor (C₂₁' x₂) (C₂₁' x₁) G}
  → {G₂₂' : DependentFunctor (C₂₂' x₂) (C₂₂' x₁) (chain-functor-snoc G₂₁')}
  → (s₁ : DependentSplitFunctorSquare G₁₁' G₂₁' (F₁ x₂) (F₁ x₁))
  → x₁ ≡ x₂
  → ChainFunctorIdentity G
  → DependentFunctorIdentity G₁₁'
  → DependentFunctorIdentity G₂₁'
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
  → ChainFunctorCompose I J K
  → DependentFunctorCompose I₁₁' J₁₁' K₁₁'
  → DependentFunctorCompose I₂₁' J₂₁' K₂₁'
  → DependentFunctorCompose I₂₂' J₂₂' K₂₂'
  → DependentFunctorCompose
    (dependent-functor-sigma-sum I₂₂' s₁)
    (dependent-functor-sigma-sum J₂₂' t₁)
    (dependent-functor-sigma-sum K₂₂' u₁)

dependent-functor-compose-sigma-sum'
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
  → {I : ChainFunctor D (E x₂)}
  → {J : ChainFunctor C D}
  → {K : ChainFunctor C (E x₁)}
  → {I₁₁' : DependentFunctor D₁₁' (E₁₁' x₂) I}
  → {I₂₁' : DependentFunctor D₂₁' (E₂₁' x₂) I}
  → {J₁₁' : DependentFunctor C₁₁' D₁₁' J}
  → {J₂₁' : DependentFunctor C₂₁' D₂₁' J}
  → {K₁₁' : DependentFunctor C₁₁' (E₁₁' x₁) K}
  → {K₂₁' : DependentFunctor C₂₁' (E₂₁' x₁) K}
  → {I₂₂' : DependentFunctor D₂₂' (E₂₂' x₂) (chain-functor-snoc I₂₁')}
  → {J₂₂' : DependentFunctor C₂₂' D₂₂' (chain-functor-snoc J₂₁')}
  → {K₂₂' : DependentFunctor C₂₂' (E₂₂' x₁) (chain-functor-snoc K₂₁')}
  → (s₁ : DependentSplitFunctorSquare I₁₁' I₂₁' G₁ (H₁ x₂))
  → (t₁ : DependentSplitFunctorSquare J₁₁' J₂₁' F₁ G₁)
  → (u₁ : DependentSplitFunctorSquare K₁₁' K₂₁' F₁ (H₁ x₁))
  → x₁ ≡ x₂
  → ChainFunctorCompose I J K
  → DependentFunctorCompose I₁₁' J₁₁' K₁₁'
  → DependentFunctorCompose I₂₁' J₂₁' K₂₁'
  → DependentFunctorCompose I₂₂' J₂₂' K₂₂'
  → DependentFunctorCompose
    (dependent-functor-sigma-sum I₂₂' s₁)
    (dependent-functor-sigma-sum J₂₂' t₁)
    (dependent-functor-sigma-sum K₂₂' u₁)

-- ### DependentFunctorSquare

dependent-functor-square-sigma-sum
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁₁₁' C₂₁₁' : DependentCategory C₁}
  → {C₁₁₂' C₂₁₂' : DependentCategory C₂}
  → {D₁₁₁' D₂₁₁' : DependentCategory D₁}
  → {D₁₁₂' D₂₁₂' : DependentCategory D₂}
  → {C₂₂₁' : DependentCategory (chain-category-snoc C₂₁₁')}
  → {C₂₂₂' : DependentCategory (chain-category-snoc C₂₁₂')}
  → {D₂₂₁' : DependentCategory (chain-category-snoc D₂₁₁')}
  → {D₂₂₂' : DependentCategory (chain-category-snoc D₂₁₂')}
  → {F₁₁ : DependentSplitFunctor C₁₁₁' C₂₁₁'}
  → {F₁₂ : DependentSplitFunctor C₁₁₂' C₂₁₂'}
  → {G₁₁ : DependentSplitFunctor D₁₁₁' D₂₁₁'}
  → {G₁₂ : DependentSplitFunctor D₁₁₂' D₂₁₂'}
  → {H : ChainFunctor C₁ C₂}
  → {I : ChainFunctor D₁ D₂}
  → {J₁ : ChainFunctor C₁ D₁}
  → {J₂ : ChainFunctor C₂ D₂}
  → {H₁₁' : DependentFunctor C₁₁₁' C₁₁₂' H}
  → {H₂₁' : DependentFunctor C₂₁₁' C₂₁₂' H}
  → {I₁₁' : DependentFunctor D₁₁₁' D₁₁₂' I}
  → {I₂₁' : DependentFunctor D₂₁₁' D₂₁₂' I}
  → {J₁₁₁' : DependentFunctor C₁₁₁' D₁₁₁' J₁}
  → {J₁₁₂' : DependentFunctor C₁₁₂' D₁₁₂' J₂}
  → {J₂₁₁' : DependentFunctor C₂₁₁' D₂₁₁' J₁}
  → {J₂₁₂' : DependentFunctor C₂₁₂' D₂₁₂' J₂}
  → {H₂₂' : DependentFunctor C₂₂₁' C₂₂₂' (chain-functor-snoc H₂₁')}
  → {I₂₂' : DependentFunctor D₂₂₁' D₂₂₂' (chain-functor-snoc I₂₁')}
  → {J₂₂₁' : DependentFunctor C₂₂₁' D₂₂₁' (chain-functor-snoc J₂₁₁')}
  → {J₂₂₂' : DependentFunctor C₂₂₂' D₂₂₂' (chain-functor-snoc J₂₁₂')}
  → (s₁ : DependentSplitFunctorSquare H₁₁' H₂₁' F₁₁ F₁₂)
  → (t₁ : DependentSplitFunctorSquare I₁₁' I₂₁' G₁₁ G₁₂)
  → (u₁₁ : DependentSplitFunctorSquare J₁₁₁' J₂₁₁' F₁₁ G₁₁)
  → (u₁₂ : DependentSplitFunctorSquare J₁₁₂' J₂₁₂' F₁₂ G₁₂)
  → ChainFunctorSquare H I J₁ J₂
  → DependentFunctorSquare H₁₁' I₁₁' J₁₁₁' J₁₁₂'
  → DependentFunctorSquare H₂₁' I₂₁' J₂₁₁' J₂₁₂'
  → DependentFunctorSquare H₂₂' I₂₂' J₂₂₁' J₂₂₂'
  → DependentFunctorSquare
    (dependent-functor-sigma-sum H₂₂' s₁)
    (dependent-functor-sigma-sum I₂₂' t₁)
    (dependent-functor-sigma-sum J₂₂₁' u₁₁)
    (dependent-functor-sigma-sum J₂₂₂' u₁₂)

dependent-functor-square-sigma-sum'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁₁₁' C₂₁₁' : DependentCategory C₁}
  → {C₁₁₂' C₂₁₂' : DependentCategory C₂}
  → {D₁₁₁' D₂₁₁' : DependentCategory D₁}
  → (D₁₁₂' D₂₁₂' : (x : A) → DependentCategory (D₂ x))
  → {C₂₂₁' : DependentCategory (chain-category-snoc C₂₁₁')}
  → {C₂₂₂' : DependentCategory (chain-category-snoc C₂₁₂')}
  → {D₂₂₁' : DependentCategory (chain-category-snoc D₂₁₁')}
  → (D₂₂₂' : (x : A) → DependentCategory (chain-category-snoc (D₂₁₂' x)))
  → {F₁₁ : DependentSplitFunctor C₁₁₁' C₂₁₁'}
  → {F₁₂ : DependentSplitFunctor C₁₁₂' C₂₁₂'}
  → {G₁₁ : DependentSplitFunctor D₁₁₁' D₂₁₁'}
  → (G₁₂ : (x : A) → DependentSplitFunctor (D₁₁₂' x) (D₂₁₂' x))
  → {H : ChainFunctor C₁ C₂}
  → {I : ChainFunctor D₁ (D₂ x₂)}
  → {J₁ : ChainFunctor C₁ D₁}
  → {J₂ : ChainFunctor C₂ (D₂ x₁)}
  → {H₁₁' : DependentFunctor C₁₁₁' C₁₁₂' H}
  → {H₂₁' : DependentFunctor C₂₁₁' C₂₁₂' H}
  → {I₁₁' : DependentFunctor D₁₁₁' (D₁₁₂' x₂) I}
  → {I₂₁' : DependentFunctor D₂₁₁' (D₂₁₂' x₂) I}
  → {J₁₁₁' : DependentFunctor C₁₁₁' D₁₁₁' J₁}
  → {J₁₁₂' : DependentFunctor C₁₁₂' (D₁₁₂' x₁) J₂}
  → {J₂₁₁' : DependentFunctor C₂₁₁' D₂₁₁' J₁}
  → {J₂₁₂' : DependentFunctor C₂₁₂' (D₂₁₂' x₁) J₂}
  → {H₂₂' : DependentFunctor C₂₂₁' C₂₂₂' (chain-functor-snoc H₂₁')}
  → {I₂₂' : DependentFunctor D₂₂₁' (D₂₂₂' x₂) (chain-functor-snoc I₂₁')}
  → {J₂₂₁' : DependentFunctor C₂₂₁' D₂₂₁' (chain-functor-snoc J₂₁₁')}
  → {J₂₂₂' : DependentFunctor C₂₂₂' (D₂₂₂' x₁) (chain-functor-snoc J₂₁₂')}
  → (s₁ : DependentSplitFunctorSquare H₁₁' H₂₁' F₁₁ F₁₂)
  → (t₁ : DependentSplitFunctorSquare I₁₁' I₂₁' G₁₁ (G₁₂ x₂))
  → (u₁₁ : DependentSplitFunctorSquare J₁₁₁' J₂₁₁' F₁₁ G₁₁)
  → (u₁₂ : DependentSplitFunctorSquare J₁₁₂' J₂₁₂' F₁₂ (G₁₂ x₁))
  → x₁ ≡ x₂
  → ChainFunctorSquare H I J₁ J₂
  → DependentFunctorSquare H₁₁' I₁₁' J₁₁₁' J₁₁₂'
  → DependentFunctorSquare H₂₁' I₂₁' J₂₁₁' J₂₁₂'
  → DependentFunctorSquare H₂₂' I₂₂' J₂₂₁' J₂₂₂'
  → DependentFunctorSquare
    (dependent-functor-sigma-sum H₂₂' s₁)
    (dependent-functor-sigma-sum I₂₂' t₁)
    (dependent-functor-sigma-sum J₂₂₁' u₁₁)
    (dependent-functor-sigma-sum J₂₂₂' u₁₂)

-- ## Definitions

-- ### DependentCategory

dependent-category-sigma-sum {n = zero} C₂₂' F₁
  = category-sigma-sum C₂₂' F₁

dependent-category-sigma-sum {n = suc _}
  {C = C} {C₁₁' = C₁₁'} {C₂₁' = C₂₁'} C₂₂' F₁
  = record
  { category
    = λ x → dependent-category-sigma-sum
      (DependentCategory.category C₂₂' x)
      (DependentSplitFunctor.split-functor F₁ x)
  ; functor
    = λ f → dependent-functor-sigma-sum
      (DependentCategory.functor C₂₂' f)
      (DependentSplitFunctor.split-functor-square F₁ f)
  ; functor-equal
    = λ {_} {_} {f₁} {f₂} p → dependent-functor-equal-sigma-sum
      (DependentSplitFunctor.split-functor-square F₁ f₁)
      (DependentSplitFunctor.split-functor-square F₁ f₂)
      (ChainCategory.functor-equal C p)
      (DependentCategory.functor-equal C₁₁' p)
      (DependentCategory.functor-equal C₂₁' p)
      (DependentCategory.functor-equal C₂₂' p)
  ; functor-identity
    = λ x → dependent-functor-identity-sigma-sum
      (DependentSplitFunctor.split-functor-square F₁
        (ChainCategory.identity C x))
      (ChainCategory.functor-identity C x)
      (DependentCategory.functor-identity C₁₁' x)
      (DependentCategory.functor-identity C₂₁' x)
      (DependentCategory.functor-identity C₂₂' x)
  ; functor-compose
    = λ f g → dependent-functor-compose-sigma-sum
      (DependentSplitFunctor.split-functor-square F₁ f)
      (DependentSplitFunctor.split-functor-square F₁ g)
      (DependentSplitFunctor.split-functor-square F₁
        (ChainCategory.compose C f g))
      (ChainCategory.functor-compose C f g)
      (DependentCategory.functor-compose C₁₁' f g)
      (DependentCategory.functor-compose C₂₁' f g)
      (DependentCategory.functor-compose C₂₂' f g)
  }

-- ### DependentFunctor

dependent-functor-sigma-sum {n = zero} H₂₂' s₁
  = functor-sigma-sum H₂₂' s₁

dependent-functor-sigma-sum {n = suc _}
  {F₁ = F₁} {G₁ = G₁} {H = H} {H₁₁' = H₁₁'} {H₂₁' = H₂₁'} H₂₂' s₁
  = record
  { functor
    = λ x → dependent-functor-sigma-sum
      (DependentFunctor.functor H₂₂' x)
      (DependentSplitFunctorSquare.split-functor s₁ x)
  ; functor-square
    = λ {x} {y} f → dependent-functor-square-sigma-sum
      (DependentSplitFunctor.split-functor-square F₁ f)
      (DependentSplitFunctor.split-functor-square G₁ (ChainFunctor.map H f))
      (DependentSplitFunctorSquare.split-functor s₁ x)
      (DependentSplitFunctorSquare.split-functor s₁ y)
      (ChainFunctor.functor-square H f)
      (DependentFunctor.functor-square H₁₁' f)
      (DependentFunctor.functor-square H₂₁' f)
      (DependentFunctor.functor-square H₂₂' f)
  }

-- ### DependentFunctorEqual

dependent-functor-equal-sigma-sum {n = zero} s₁₁ s₂₁ _ p₁₁' p₂₁' p₂₂'
  = functor-equal-sigma-sum s₁₁ s₂₁ p₁₁' p₂₁' p₂₂'

dependent-functor-equal-sigma-sum {n = suc _}
  {D = D} {D₁₁' = D₁₁'} {D₂₁' = D₂₁'} {D₂₂' = D₂₂'} 
  {G₁ = G₁} s₁₁ s₂₁ p p₁₁' p₂₁' p₂₂'
  = record
  { functor
    = λ x → dependent-functor-equal-sigma-sum'
      (ChainCategory.category' D)
      (DependentCategory.category D₁₁')
      (DependentCategory.category D₂₁')
      (DependentCategory.category D₂₂')
      (DependentSplitFunctor.split-functor G₁)
      (DependentSplitFunctorSquare.split-functor s₁₁ x)
      (DependentSplitFunctorSquare.split-functor s₂₁ x)
      (ChainFunctorEqual.base p x)
      (ChainFunctorEqual.functor' p x)
      (DependentFunctorEqual.functor p₁₁' x)
      (DependentFunctorEqual.functor p₂₁' x)
      (DependentFunctorEqual.functor p₂₂' x)
  }

dependent-functor-equal-sigma-sum' _ _ _ _ _ s₁₁ s₂₁ refl
  = dependent-functor-equal-sigma-sum s₁₁ s₂₁

-- ### DependentFunctorIdentity

dependent-functor-identity-sigma-sum {n = zero} s₁ _ p₁₁' p₂₁' p₂₂'
  = functor-identity-sigma-sum s₁ p₁₁' p₂₁' p₂₂'

dependent-functor-identity-sigma-sum {n = suc _}
  {C = C} {C₁₁' = C₁₁'} {C₂₁' = C₂₁'} {C₂₂' = C₂₂'}
  {F₁ = F₁} s₁ p p₁₁' p₂₁' p₂₂'
  = record
  { functor
    = λ x → dependent-functor-identity-sigma-sum'
      (ChainCategory.category' C)
      (DependentCategory.category C₁₁')
      (DependentCategory.category C₂₁')
      (DependentCategory.category C₂₂')
      (DependentSplitFunctor.split-functor F₁)
      (DependentSplitFunctorSquare.split-functor s₁ x)
      (ChainFunctorIdentity.base p x)
      (ChainFunctorIdentity.functor' p x)
      (DependentFunctorIdentity.functor p₁₁' x)
      (DependentFunctorIdentity.functor p₂₁' x)
      (DependentFunctorIdentity.functor p₂₂' x)
  }

dependent-functor-identity-sigma-sum' _ _ _ _ _ s₁ refl
  = dependent-functor-identity-sigma-sum s₁

-- ### DependentFunctorCompose

dependent-functor-compose-sigma-sum {n = zero} s₁ t₁ u₁ _ p₁₁' p₂₁' p₂₂'
  = functor-compose-sigma-sum s₁ t₁ u₁ p₁₁' p₂₁' p₂₂'

dependent-functor-compose-sigma-sum {n = suc _}
  {E = E} {E₁₁' = E₁₁'} {E₂₁' = E₂₁'} {E₂₂' = E₂₂'}
  {H₁ = H₁} {J = J} s₁ t₁ u₁ p p₁₁' p₂₁' p₂₂'
  = record
  { functor
    = λ x → dependent-functor-compose-sigma-sum'
      (ChainCategory.category' E)
      (DependentCategory.category E₁₁')
      (DependentCategory.category E₂₁')
      (DependentCategory.category E₂₂')
      (DependentSplitFunctor.split-functor H₁)
      (DependentSplitFunctorSquare.split-functor s₁ (ChainFunctor.base J x))
      (DependentSplitFunctorSquare.split-functor t₁ x)
      (DependentSplitFunctorSquare.split-functor u₁ x)
      (ChainFunctorCompose.base p x)
      (ChainFunctorCompose.functor' p x)
      (DependentFunctorCompose.functor p₁₁' x)
      (DependentFunctorCompose.functor p₂₁' x)
      (DependentFunctorCompose.functor p₂₂' x)
  }

dependent-functor-compose-sigma-sum' _ _ _ _ _ s₁ t₁ u₁ refl
  = dependent-functor-compose-sigma-sum s₁ t₁ u₁

-- ### DependentFunctorSquare

dependent-functor-square-sigma-sum {n = zero} s₁ t₁ u₁₁ u₂₁ _ v₁₁' v₂₁' v₂₂'
  = functor-square-sigma-sum s₁ t₁ u₁₁ u₂₁ v₁₁' v₂₁' v₂₂'

dependent-functor-square-sigma-sum {n = suc _}
  {D₂ = D₂} {D₁₁₂' = D₁₁₂'} {D₂₁₂' = D₂₁₂'} {D₂₂₂' = D₂₂₂'}
  {G₁₂ = G₁₂} {H = H} {J₁ = J₁} s₁ t₁ u₁₁ u₂₁ v v₁₁' v₂₁' v₂₂'
  = record
  { functor
    = λ x₁ → dependent-functor-square-sigma-sum'
      (ChainCategory.category' D₂)
      (DependentCategory.category D₁₁₂')
      (DependentCategory.category D₂₁₂')
      (DependentCategory.category D₂₂₂')
      (DependentSplitFunctor.split-functor G₁₂)
      (DependentSplitFunctorSquare.split-functor s₁ x₁)
      (DependentSplitFunctorSquare.split-functor t₁ (ChainFunctor.base J₁ x₁))
      (DependentSplitFunctorSquare.split-functor u₁₁ x₁)
      (DependentSplitFunctorSquare.split-functor u₂₁ (ChainFunctor.base H x₁))
      (ChainFunctorSquare.base v x₁)
      (ChainFunctorSquare.functor' v x₁)
      (DependentFunctorSquare.functor v₁₁' x₁)
      (DependentFunctorSquare.functor v₂₁' x₁)
      (DependentFunctorSquare.functor v₂₂' x₁)
  }

dependent-functor-square-sigma-sum' _ _ _ _ _ s₁ t₁ u₁₁ u₂₁ refl
  = dependent-functor-square-sigma-sum s₁ t₁ u₁₁ u₂₁

