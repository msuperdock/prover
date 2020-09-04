module Prover.Category.Dependent where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Dependent1
  using (Dependent₁Category; Dependent₁Functor; Dependent₁FunctorCompose;
    Dependent₁FunctorIdentity; Dependent₁FunctorSquare)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types
  
  -- #### DependentCategory
  
  data DependentCategory
    : {n : ℕ}
    → ChainCategory n
    → Set₁
    
  -- #### DependentFunctor
  
  data DependentFunctor
    : {n : ℕ}
    → {C D : ChainCategory n}
    → DependentCategory C
    → DependentCategory D
    → ChainFunctor C D
    → Set
    
  -- #### DependentFunctorIdentity
  
  data DependentFunctorIdentity
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory n}
    → {C₁' : DependentCategory C₁}
    → {C₂' : DependentCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → DependentFunctor C₁' C₂' F
    → Set
    
  -- #### DependentFunctorCompose
  
  data DependentFunctorCompose
    : {n : ℕ}
    → {C D E₁ E₂ : ChainCategory n}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {E₁' : DependentCategory E₁}
    → {E₂' : DependentCategory E₂}
    → {F : ChainFunctor D E₁}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E₂}
    → DependentFunctor D' E₁' F
    → DependentFunctor C' D' G
    → DependentFunctor C' E₂' H
    → Set
    
  -- #### DependentFunctorSquare
  
  data DependentFunctorSquare
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
    → {C₁' : DependentCategory C₁}
    → {C₂' : DependentCategory C₂}
    → {D₁' : DependentCategory D₁}
    → {D₂' : DependentCategory D₂}
    → {D₃' : DependentCategory D₃}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₃}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → DependentFunctor C₁' C₂' F
    → DependentFunctor D₁' D₃' G
    → DependentFunctor C₁' D₁' H₁
    → DependentFunctor C₂' D₂' H₂
    → Set
    
  -- ### Interface

  -- #### DependentCategory

  dependent-category₀
    : {C : ChainCategory zero}
    → DependentCategory C
    → Category

  dependent-category-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → DependentCategory C
    → (x : ChainCategory.Object C)
    → DependentCategory
      (ChainCategory.tail C x)

  dependent-category-dependent-functor
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : DependentCategory C)
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → DependentFunctor
      (dependent-category-tail C' x)
      (dependent-category-tail C' y)
      (ChainCategory.chain-functor C f)

  dependent-category-dependent-functor-identity
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : DependentCategory C)
    → (x : ChainCategory.Object C)
    → DependentFunctorIdentity
      (dependent-category-dependent-functor C' (ChainCategory.identity C x))

  dependent-category-dependent-functor-compose
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : DependentCategory C)
    → {x y z : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C y z)
    → (g : ChainCategory.Arrow C x y)
    → DependentFunctorCompose
      (dependent-category-dependent-functor C' f)
      (dependent-category-dependent-functor C' g)
      (dependent-category-dependent-functor C' (ChainCategory.compose C f g))

  -- #### DependentFunctor

  dependent-functor₀
    : {C D : ChainCategory zero}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {F : ChainFunctor C D}
    → DependentFunctor C' D' F
    → Functor
      (dependent-category₀ C')
      (dependent-category₀ D')

  dependent-functor-tail
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {F : ChainFunctor C D}
    → DependentFunctor C' D' F
    → (x : ChainCategory.Object C)
    → DependentFunctor
      (dependent-category-tail C' x)
      (dependent-category-tail D' (ChainFunctor.base F x))
      (ChainFunctor.tail F x)

  dependent-functor-dependent-functor-square
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {F : ChainFunctor C D}
    → (F' : DependentFunctor C' D' F)
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → DependentFunctorSquare
      (dependent-category-dependent-functor C' f)
      (dependent-category-dependent-functor D' (ChainFunctor.map F f))
      (dependent-functor-tail F' x)
      (dependent-functor-tail F' y)

  -- #### DependentFunctorIdentity

  dependent-functor-identity₀
    : {C : ChainCategory zero}
    → {C' : DependentCategory C}
    → {F : ChainFunctor C C}
    → {F' : DependentFunctor C' C' F}
    → DependentFunctorIdentity F'
    → FunctorIdentity
      (dependent-functor₀ F')

  dependent-functor-identity₀-eq
    : {A : Set}
    → {x₁ x₂ : A}
    → (C : A → ChainCategory zero)
    → (C' : (x : A) → DependentCategory (C x))
    → {F : ChainFunctor (C x₁) (C x₂)}
    → {F' : DependentFunctor (C' x₁) (C' x₂) F}
    → x₂ ≡ x₁
    → DependentFunctorIdentity F'
    → FunctorIdentity
      (dependent-functor₀ F')

  dependent-functor-identity-head
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {F : ChainFunctor C C}
    → {F' : DependentFunctor C' C' F}
    → DependentFunctorIdentity F'
    → FunctorIdentity
      (ChainFunctor.head F)

  dependent-functor-identity-base
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {F : ChainFunctor C C}
    → {F' : DependentFunctor C' C' F}
    → DependentFunctorIdentity F'
    → (x : ChainCategory.Object C)
    → ChainFunctor.base F x ≡ x

  dependent-functor-identity-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {F : ChainFunctor C C}
    → {F' : DependentFunctor C' C' F}
    → DependentFunctorIdentity F'
    → (x : ChainCategory.Object C)
    → DependentFunctorIdentity
      (dependent-functor-tail F' x)

  -- #### DependentFunctorCompose
  
  dependent-functor-compose₀
    : {C D E : ChainCategory zero}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {E' : DependentCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : DependentFunctor D' E' F}
    → {G' : DependentFunctor C' D' G}
    → {H' : DependentFunctor C' E' H}
    → DependentFunctorCompose F' G' H'
    → FunctorCompose
      (dependent-functor₀ F')
      (dependent-functor₀ G')
      (dependent-functor₀ H')

  dependent-functor-compose₀-eq
    : {A : Set}
    → {x₁ x₂ : A}
    → {C D : ChainCategory zero}
    → (E : A → ChainCategory zero)
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → (E' : (x : A) → DependentCategory (E x))
    → {F : ChainFunctor D (E x₁)}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C (E x₂)}
    → {F' : DependentFunctor D' (E' x₁) F}
    → {G' : DependentFunctor C' D' G}
    → {H' : DependentFunctor C' (E' x₂) H}
    → x₂ ≡ x₁
    → DependentFunctorCompose F' G' H'
    → FunctorCompose
      (dependent-functor₀ F')
      (dependent-functor₀ G')
      (dependent-functor₀ H')

  dependent-functor-compose-head
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {E' : DependentCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : DependentFunctor D' E' F}
    → {G' : DependentFunctor C' D' G}
    → {H' : DependentFunctor C' E' H}
    → DependentFunctorCompose F' G' H'
    → FunctorCompose
      (ChainFunctor.head F)
      (ChainFunctor.head G)
      (ChainFunctor.head H)

  dependent-functor-compose-base
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {E' : DependentCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : DependentFunctor D' E' F}
    → {G' : DependentFunctor C' D' G}
    → {H' : DependentFunctor C' E' H}
    → DependentFunctorCompose F' G' H'
    → (x : ChainCategory.Object C)
    → ChainFunctor.base H x ≡ ChainFunctor.base F (ChainFunctor.base G x)

  dependent-functor-compose-tail
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {D' : DependentCategory D}
    → {E' : DependentCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : DependentFunctor D' E' F}
    → {G' : DependentFunctor C' D' G}
    → {H' : DependentFunctor C' E' H}
    → DependentFunctorCompose F' G' H'
    → (x : ChainCategory.Object C)
    → DependentFunctorCompose
      (dependent-functor-tail F' (ChainFunctor.base G x))
      (dependent-functor-tail G' x)
      (dependent-functor-tail H' x)

  -- #### DependentFunctorSquare

  dependent-functor-square₀
    : {C₁ C₂ D₁ D₂ : ChainCategory zero}
    → {C₁' : DependentCategory C₁}
    → {C₂' : DependentCategory C₂}
    → {D₁' : DependentCategory D₁}
    → {D₂' : DependentCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : DependentFunctor C₁' C₂' F}
    → {G' : DependentFunctor D₁' D₂' G}
    → {H₁' : DependentFunctor C₁' D₁' H₁}
    → {H₂' : DependentFunctor C₂' D₂' H₂}
    → DependentFunctorSquare F' G' H₁' H₂'
    → FunctorSquare
      (dependent-functor₀ F')
      (dependent-functor₀ G')
      (dependent-functor₀ H₁')
      (dependent-functor₀ H₂')

  dependent-functor-square₀-eq
    : {A : Set}
    → {x₁ x₂ : A}
    → {C₁ C₂ D₁ : ChainCategory zero}
    → (D₂ : A → ChainCategory zero)
    → {C₁' : DependentCategory C₁}
    → {C₂' : DependentCategory C₂}
    → {D₁' : DependentCategory D₁}
    → (D₂' : (x : A) → DependentCategory (D₂ x))
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ (D₂ x₁)}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ (D₂ x₂)}
    → {F' : DependentFunctor C₁' C₂' F}
    → {G' : DependentFunctor D₁' (D₂' x₁) G}
    → {H₁' : DependentFunctor C₁' D₁' H₁}
    → {H₂' : DependentFunctor C₂' (D₂' x₂) H₂}
    → x₂ ≡ x₁
    → DependentFunctorSquare F' G' H₁' H₂'
    → FunctorSquare
      (dependent-functor₀ F')
      (dependent-functor₀ G')
      (dependent-functor₀ H₁')
      (dependent-functor₀ H₂')

  dependent-functor-square-head
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : DependentCategory C₁}
    → {C₂' : DependentCategory C₂}
    → {D₁' : DependentCategory D₁}
    → {D₂' : DependentCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : DependentFunctor C₁' C₂' F}
    → {G' : DependentFunctor D₁' D₂' G}
    → {H₁' : DependentFunctor C₁' D₁' H₁}
    → {H₂' : DependentFunctor C₂' D₂' H₂}
    → DependentFunctorSquare F' G' H₁' H₂'
    → FunctorSquare
      (ChainFunctor.head F)
      (ChainFunctor.head G)
      (ChainFunctor.head H₁)
      (ChainFunctor.head H₂)

  dependent-functor-square-base
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : DependentCategory C₁}
    → {C₂' : DependentCategory C₂}
    → {D₁' : DependentCategory D₁}
    → {D₂' : DependentCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : DependentFunctor C₁' C₂' F}
    → {G' : DependentFunctor D₁' D₂' G}
    → {H₁' : DependentFunctor C₁' D₁' H₁}
    → {H₂' : DependentFunctor C₂' D₂' H₂}
    → DependentFunctorSquare F' G' H₁' H₂'
    → (x₁ : ChainCategory.Object C₁)
    → ChainFunctor.base H₂ (ChainFunctor.base F x₁)
      ≡ ChainFunctor.base G (ChainFunctor.base H₁ x₁)

  dependent-functor-square-tail
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : DependentCategory C₁}
    → {C₂' : DependentCategory C₂}
    → {D₁' : DependentCategory D₁}
    → {D₂' : DependentCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : DependentFunctor C₁' C₂' F}
    → {G' : DependentFunctor D₁' D₂' G}
    → {H₁' : DependentFunctor C₁' D₁' H₁}
    → {H₂' : DependentFunctor C₂' D₂' H₂}
    → DependentFunctorSquare F' G' H₁' H₂'
    → (x₁ : ChainCategory.Object C₁)
    → DependentFunctorSquare
      (dependent-functor-tail F' x₁)
      (dependent-functor-tail G' (ChainFunctor.base H₁ x₁))
      (dependent-functor-tail H₁' x₁)
      (dependent-functor-tail H₂' (ChainFunctor.base F x₁))

  -- ### Definitions
  
  -- #### DependentCategory
  
  data DependentCategory where
  
    nil
      : {C : ChainCategory zero}
      → Category
      → DependentCategory C

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → (C' : (x : ChainCategory.Object C)
        → DependentCategory
          (ChainCategory.tail C x))
      → (F : {x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → DependentFunctor (C' x) (C' y)
          (ChainCategory.chain-functor C f))
      → ((x : ChainCategory.Object C)
        → DependentFunctorIdentity
          (F (ChainCategory.identity C x)))
      → ({x y z : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C y z)
        → (g : ChainCategory.Arrow C x y)
        → DependentFunctorCompose (F f) (F g)
          (F (ChainCategory.compose C f g)))
      → DependentCategory C
  
  dependent-category₀ (nil C')
    = C'

  dependent-category-tail (cons C' _ _ _)
    = C'

  dependent-category-dependent-functor (cons _ F _ _)
    = F

  dependent-category-dependent-functor-identity (cons _ _ p _)
    = p

  dependent-category-dependent-functor-compose (cons _ _ _ p)
    = p

  -- #### DependentFunctor
  
  data DependentFunctor where
  
    nil
      : {C D : ChainCategory zero}
      → {C' : DependentCategory C}
      → {D' : DependentCategory D}
      → {F : ChainFunctor C D}
      → Functor
        (dependent-category₀ C')
        (dependent-category₀ D')
      → DependentFunctor C' D' F

    cons
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → {C' : DependentCategory C}
      → {D' : DependentCategory D}
      → {F : ChainFunctor C D}
      → (F' : (x : ChainCategory.Object C)
        → DependentFunctor
          (dependent-category-tail C' x)
          (dependent-category-tail D' (ChainFunctor.base F x))
          (ChainFunctor.tail F x))
      → ({x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → DependentFunctorSquare
          (dependent-category-dependent-functor C' f)
          (dependent-category-dependent-functor D' (ChainFunctor.map F f))
          (F' x)
          (F' y))
      → DependentFunctor C' D' F
  
  dependent-functor₀ (nil F')
    = F'

  dependent-functor-tail (cons F' _)
    = F'

  dependent-functor-dependent-functor-square (cons _ s)
    = s

  -- #### DependentFunctorIdentity
  
  data DependentFunctorIdentity where
  
    nil
      : {C : ChainCategory zero}
      → {C' : DependentCategory C}
      → {F : ChainFunctor C C}
      → {F' : DependentFunctor C' C' F}
      → FunctorIdentity
        (dependent-functor₀ F')
      → DependentFunctorIdentity F'

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : DependentCategory C}
      → {F : ChainFunctor C C}
      → {F' : DependentFunctor C' C' F}
      → FunctorIdentity
        (ChainFunctor.head F)
      → ((x : ChainCategory.Object C)
        → DependentFunctorIdentity
          (dependent-functor-tail F' x))
      → DependentFunctorIdentity F'

  dependent-functor-identity₀ (nil p)
    = p

  dependent-functor-identity₀-eq _ _ refl
    = dependent-functor-identity₀

  dependent-functor-identity-head (cons p _)
    = p

  dependent-functor-identity-base p
    = FunctorIdentity.base
      (dependent-functor-identity-head p)

  dependent-functor-identity-tail (cons _ p)
    = p

  -- #### DependentFunctorCompose
  
  data DependentFunctorCompose where
  
    nil
      : {C D E : ChainCategory zero}
      → {C' : DependentCategory C}
      → {D' : DependentCategory D}
      → {E' : DependentCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : DependentFunctor D' E' F}
      → {G' : DependentFunctor C' D' G}
      → {H' : DependentFunctor C' E' H}
      → FunctorCompose
        (dependent-functor₀ F')
        (dependent-functor₀ G')
        (dependent-functor₀ H')
      → DependentFunctorCompose F' G' H'

    cons
      : {n : ℕ}
      → {C D E : ChainCategory (suc n)}
      → {C' : DependentCategory C}
      → {D' : DependentCategory D}
      → {E' : DependentCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : DependentFunctor D' E' F}
      → {G' : DependentFunctor C' D' G}
      → {H' : DependentFunctor C' E' H}
      → FunctorCompose
        (ChainFunctor.head F)
        (ChainFunctor.head G)
        (ChainFunctor.head H)
      → ((x : ChainCategory.Object C)
        → DependentFunctorCompose
          (dependent-functor-tail F' (ChainFunctor.base G x))
          (dependent-functor-tail G' x)
          (dependent-functor-tail H' x))
      → DependentFunctorCompose F' G' H'

  dependent-functor-compose₀ (nil p)
    = p

  dependent-functor-compose₀-eq _ _ refl
    = dependent-functor-compose₀

  dependent-functor-compose-head (cons p _)
    = p

  dependent-functor-compose-base p
    = FunctorCompose.base
      (dependent-functor-compose-head p)

  dependent-functor-compose-tail (cons _ p)
    = p

  -- #### DependentFunctorSquare
  
  data DependentFunctorSquare where
  
    nil
      : {C₁ C₂ D₁ D₂ : ChainCategory zero}
      → {C₁' : DependentCategory C₁}
      → {C₂' : DependentCategory C₂}
      → {D₁' : DependentCategory D₁}
      → {D₂' : DependentCategory D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : DependentFunctor C₁' C₂' F}
      → {G' : DependentFunctor D₁' D₂' G}
      → {H₁' : DependentFunctor C₁' D₁' H₁}
      → {H₂' : DependentFunctor C₂' D₂' H₂}
      → FunctorSquare
        (dependent-functor₀ F')
        (dependent-functor₀ G')
        (dependent-functor₀ H₁')
        (dependent-functor₀ H₂')
      → DependentFunctorSquare F' G' H₁' H₂'

    cons
      : {n : ℕ}
      → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
      → {C₁' : DependentCategory C₁}
      → {C₂' : DependentCategory C₂}
      → {D₁' : DependentCategory D₁}
      → {D₂' : DependentCategory D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : DependentFunctor C₁' C₂' F}
      → {G' : DependentFunctor D₁' D₂' G}
      → {H₁' : DependentFunctor C₁' D₁' H₁}
      → {H₂' : DependentFunctor C₂' D₂' H₂}
      → FunctorSquare
        (ChainFunctor.head F)
        (ChainFunctor.head G)
        (ChainFunctor.head H₁)
        (ChainFunctor.head H₂)
      → ((x₁ : ChainCategory.Object C₁)
        → DependentFunctorSquare
          (dependent-functor-tail F' x₁)
          (dependent-functor-tail G' (ChainFunctor.base H₁ x₁))
          (dependent-functor-tail H₁' x₁)
          (dependent-functor-tail H₂' (ChainFunctor.base F x₁)))
      → DependentFunctorSquare F' G' H₁' H₂'

  dependent-functor-square₀ (nil s)
    = s

  dependent-functor-square₀-eq _ _ refl
    = dependent-functor-square₀

  dependent-functor-square-head (cons s _)
    = s

  dependent-functor-square-base s
    = FunctorSquare.base
      (dependent-functor-square-head s)

  dependent-functor-square-tail (cons _ s)
    = s

  -- ### Destruction

  -- #### DependentCategory

  module _
    {C : ChainCategory (suc zero)}
    where

    module DependentCategory₁
      (C' : DependentCategory C)
      where

      category
        : Category.Object (ChainCategory.head C)
        → Category
      category x
        = dependent-category₀
          (dependent-category-tail C' x)

      functor
        : {x y : Category.Object (ChainCategory.head C)}
        → Category.Arrow (ChainCategory.head C) x y
        → Functor
          (category x)
          (category y)
      functor f
        = dependent-functor₀
          (dependent-category-dependent-functor C' f)

      abstract

        functor-identity
          : (x : Category.Object (ChainCategory.head C))
          → FunctorIdentity
            (functor (Category.identity (ChainCategory.head C) x))
        functor-identity x
          = dependent-functor-identity₀
            (dependent-category-dependent-functor-identity C' x)

        functor-compose
          : {x y z : Category.Object (ChainCategory.head C)}
          → (f : Category.Arrow (ChainCategory.head C) y z)
          → (g : Category.Arrow (ChainCategory.head C) x y)
          → FunctorCompose
            (functor f)
            (functor g)
            (functor (Category.compose (ChainCategory.head C) f g))
        functor-compose f g
          = dependent-functor-compose₀
            (dependent-category-dependent-functor-compose C' f g)

    dependent-category₁
      : DependentCategory C
      → Dependent₁Category
        (ChainCategory.head C)
    dependent-category₁ C'
      = record {DependentCategory₁ C'}

  -- #### DependentFunctor

  module _
    {C D : ChainCategory (suc zero)}
    {C' : DependentCategory C}
    {D' : DependentCategory D}
    {F : ChainFunctor C D}
    where

    module DependentFunctor₁
      (F' : DependentFunctor C' D' F)
      where

      functor
        : Functor
          (ChainCategory.head C)
          (ChainCategory.head D)
      functor
        = ChainFunctor.head F

      open Functor functor

      functor'
        : (x : Category.Object (ChainCategory.head C))
        → Functor
          (Dependent₁Category.category (dependent-category₁ C') x)
          (Dependent₁Category.category (dependent-category₁ D') (base x))
      functor' x
        = dependent-functor₀
          (dependent-functor-tail F' x)

      abstract

        functor-square
          : {x y : Category.Object (ChainCategory.head C)}
          → (f : Category.Arrow (ChainCategory.head C) x y)
          → FunctorSquare
            (Dependent₁Category.functor (dependent-category₁ C') f)
            (Dependent₁Category.functor (dependent-category₁ D') (map f))
            (functor' x)
            (functor' y)
        functor-square f
          = dependent-functor-square₀
            (dependent-functor-dependent-functor-square F' f)

    dependent-functor₁
      : DependentFunctor C' D' F
      → Dependent₁Functor
        (dependent-category₁ C')
        (dependent-category₁ D')
    dependent-functor₁ F'
      = record {DependentFunctor₁ F'}

  -- #### DependentFunctorIdentity

  module _
    {C : ChainCategory (suc zero)}
    {C' : DependentCategory C}
    {F : ChainFunctor C C}
    {F' : DependentFunctor C' C' F}
    where

    module DependentFunctorIdentity₁
      (p : DependentFunctorIdentity F')
      where

      functor
        : FunctorIdentity
          (Dependent₁Functor.functor (dependent-functor₁ F'))
      functor
        = dependent-functor-identity-head p
          
      functor'
        : (x : Category.Object (ChainCategory.head C))
        → FunctorIdentity
          (Dependent₁Functor.functor' (dependent-functor₁ F') x)
      functor' x
        = dependent-functor-identity₀-eq
          (ChainCategory.tail C)
          (dependent-category-tail C')
          (dependent-functor-identity-base p x)
          (dependent-functor-identity-tail p x)

    dependent-functor-identity₁
      : DependentFunctorIdentity F'
      → Dependent₁FunctorIdentity
        (dependent-functor₁ F')
    dependent-functor-identity₁ p
      = record {DependentFunctorIdentity₁ p}

  -- #### DependentFunctorCompose

  module _
    {C D E : ChainCategory (suc zero)}
    {C' : DependentCategory C}
    {D' : DependentCategory D}
    {E' : DependentCategory E}
    {F : ChainFunctor D E}
    {G : ChainFunctor C D}
    {H : ChainFunctor C E}
    {F' : DependentFunctor D' E' F}
    {G' : DependentFunctor C' D' G}
    {H' : DependentFunctor C' E' H}
    where

    module DependentFunctorCompose₁
      (p : DependentFunctorCompose F' G' H')
      where

      functor
        : FunctorCompose
          (Dependent₁Functor.functor (dependent-functor₁ F'))
          (Dependent₁Functor.functor (dependent-functor₁ G'))
          (Dependent₁Functor.functor (dependent-functor₁ H'))
      functor
        = dependent-functor-compose-head p

      functor'
        : (x : Category.Object (ChainCategory.head C))
        → FunctorCompose
          (Dependent₁Functor.functor' (dependent-functor₁ F')
            (Dependent₁Functor.base (dependent-functor₁ G') x))
          (Dependent₁Functor.functor' (dependent-functor₁ G') x)
          (Dependent₁Functor.functor' (dependent-functor₁ H') x)
      functor' x
        = dependent-functor-compose₀-eq
          (ChainCategory.tail E)
          (dependent-category-tail E')
          (dependent-functor-compose-base p x)
          (dependent-functor-compose-tail p x)

    dependent-functor-compose₁
      : DependentFunctorCompose F' G' H'
      → Dependent₁FunctorCompose
        (dependent-functor₁ F')
        (dependent-functor₁ G')
        (dependent-functor₁ H')
    dependent-functor-compose₁ p
      = record {DependentFunctorCompose₁ p}

  -- #### DependentFunctorSquare

  module _
    {C₁ C₂ D₁ D₂ : ChainCategory (suc zero)}
    {C₁' : DependentCategory C₁}
    {C₂' : DependentCategory C₂}
    {D₁' : DependentCategory D₁}
    {D₂' : DependentCategory D₂}
    {F : ChainFunctor C₁ C₂}
    {G : ChainFunctor D₁ D₂}
    {H₁ : ChainFunctor C₁ D₁}
    {H₂ : ChainFunctor C₂ D₂}
    {F' : DependentFunctor C₁' C₂' F}
    {G' : DependentFunctor D₁' D₂' G}
    {H₁' : DependentFunctor C₁' D₁' H₁}
    {H₂' : DependentFunctor C₂' D₂' H₂}
    where

    module DependentFunctorSquare₁
      (s : DependentFunctorSquare F' G' H₁' H₂')
      where

      functor
        : FunctorSquare
          (Dependent₁Functor.functor (dependent-functor₁ F'))
          (Dependent₁Functor.functor (dependent-functor₁ G'))
          (Dependent₁Functor.functor (dependent-functor₁ H₁'))
          (Dependent₁Functor.functor (dependent-functor₁ H₂'))
      functor
        = dependent-functor-square-head s

      functor'
        : (x₁ : Category.Object (ChainCategory.head C₁))
        → FunctorSquare
          (Dependent₁Functor.functor' (dependent-functor₁ F') x₁)
          (Dependent₁Functor.functor' (dependent-functor₁ G')
            (Dependent₁Functor.base (dependent-functor₁ H₁') x₁))
          (Dependent₁Functor.functor' (dependent-functor₁ H₁') x₁)
          (Dependent₁Functor.functor' (dependent-functor₁ H₂')
            (Dependent₁Functor.base (dependent-functor₁ F') x₁))
      functor' x₁
        = dependent-functor-square₀-eq
          (ChainCategory.tail D₂)
          (dependent-category-tail D₂')
          (dependent-functor-square-base s x₁)
          (dependent-functor-square-tail s x₁)

    dependent-functor-square₁
      : DependentFunctorSquare F' G' H₁' H₂'
      → Dependent₁FunctorSquare
        (dependent-functor₁ F')
        (dependent-functor₁ G')
        (dependent-functor₁ H₁')
        (dependent-functor₁ H₂')
    dependent-functor-square₁ s
      = record {DependentFunctorSquare₁ s}

-- ## Modules

-- ### DependentCategory

DependentCategory
  : {n : ℕ}
  → ChainCategory n
  → Set₁
DependentCategory
  = Internal.DependentCategory

open Internal.DependentCategory public

open Internal public
  using (dependent-category₀; dependent-category₁)

module DependentCategory where

  open Internal public using () renaming
    ( dependent-category-tail
      to tail
    ; dependent-category-dependent-functor
      to dependent-functor
    ; dependent-category-dependent-functor-compose
      to dependent-functor-compose
    ; dependent-category-dependent-functor-identity
      to dependent-functor-identity
    )

-- ### DependentFunctor

DependentFunctor
  : {n : ℕ}
  → {C D : ChainCategory n}
  → DependentCategory C
  → DependentCategory D
  → ChainFunctor C D
  → Set
DependentFunctor
  = Internal.DependentFunctor
  
open Internal.DependentFunctor public

open Internal public
  using (dependent-functor₀; dependent-functor₁)

module DependentFunctor where

  open Internal public using () renaming
    ( dependent-functor-tail
      to tail
    ; dependent-functor-dependent-functor-square
      to dependent-functor-square
    )

-- ### DependentFunctorIdentity

DependentFunctorIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → DependentFunctor C₁' C₂' F
  → Set
DependentFunctorIdentity
  = Internal.DependentFunctorIdentity
  
open Internal.DependentFunctorIdentity public

open Internal public
  using (dependent-functor-identity₀; dependent-functor-identity₁)

module DependentFunctorIdentity where

  open Internal public using () renaming
    ( dependent-functor-identity-base
      to base
    ; dependent-functor-identity-head
      to head
    ; dependent-functor-identity-tail
      to tail
    )

-- ### DependentFunctorCompose

DependentFunctorCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {E₁' : DependentCategory E₁}
  → {E₂' : DependentCategory E₂}
  → {F : ChainFunctor D E₁}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E₂}
  → DependentFunctor D' E₁' F
  → DependentFunctor C' D' G
  → DependentFunctor C' E₂' H
  → Set
DependentFunctorCompose
  = Internal.DependentFunctorCompose
  
open Internal.DependentFunctorCompose public

open Internal public
  using (dependent-functor-compose₀; dependent-functor-compose₁)

module DependentFunctorCompose where

  open Internal public using () renaming
    ( dependent-functor-compose-base
      to base
    ; dependent-functor-compose-head
      to head
    ; dependent-functor-compose-tail
      to tail
    )

-- ### DependentFunctorSquare

DependentFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {D₁' : DependentCategory D₁}
  → {D₂' : DependentCategory D₂}
  → {D₃' : DependentCategory D₃}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₃}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → DependentFunctor C₁' C₂' F
  → DependentFunctor D₁' D₃' G
  → DependentFunctor C₁' D₁' H₁
  → DependentFunctor C₂' D₂' H₂
  → Set
DependentFunctorSquare
  = Internal.DependentFunctorSquare
  
open Internal.DependentFunctorSquare public

open Internal public
  using (dependent-functor-square₀; dependent-functor-square₁)

module DependentFunctorSquare where

  open Internal public using () renaming
    ( dependent-functor-square-base
      to base
    ; dependent-functor-square-head
      to head
    ; dependent-functor-square-tail
      to tail
    )

