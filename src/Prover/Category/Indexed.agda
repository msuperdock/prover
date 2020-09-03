module Prover.Category.Indexed where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; Functor; FunctorCompose;
    FunctorIdentity; FunctorSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types
  
  -- #### IndexedCategory
  
  data IndexedCategory
    : {n : ℕ}
    → ChainCategory n
    → Set₁
    
  -- #### IndexedFunctor
  
  data IndexedFunctor
    : {n : ℕ}
    → {C D : ChainCategory n}
    → IndexedCategory C
    → IndexedCategory D
    → ChainFunctor C D
    → Set
    
  -- #### IndexedFunctorIdentity
  
  data IndexedFunctorIdentity
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory n}
    → {C₁' : IndexedCategory C₁}
    → {C₂' : IndexedCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → IndexedFunctor C₁' C₂' F
    → Set
    
  -- #### IndexedFunctorCompose
  
  data IndexedFunctorCompose
    : {n : ℕ}
    → {C D E₁ E₂ : ChainCategory n}
    → {C' : IndexedCategory C}
    → {D' : IndexedCategory D}
    → {E₁' : IndexedCategory E₁}
    → {E₂' : IndexedCategory E₂}
    → {F : ChainFunctor D E₁}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E₂}
    → IndexedFunctor D' E₁' F
    → IndexedFunctor C' D' G
    → IndexedFunctor C' E₂' H
    → Set
    
  -- #### IndexedFunctorSquare
  
  data IndexedFunctorSquare
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
    → {C₁' : IndexedCategory C₁}
    → {C₂' : IndexedCategory C₂}
    → {D₁' : IndexedCategory D₁}
    → {D₂' : IndexedCategory D₂}
    → {D₃' : IndexedCategory D₃}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₃}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → IndexedFunctor C₁' C₂' F
    → IndexedFunctor D₁' D₃' G
    → IndexedFunctor C₁' D₁' H₁
    → IndexedFunctor C₂' D₂' H₂
    → Set
    
  -- ### Interface

  -- #### IndexedCategory

  indexed-category₀
    : {C : ChainCategory zero}
    → IndexedCategory C
    → Category

  indexed-category-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedCategory C
    → (x : ChainCategory.Object C)
    → IndexedCategory
      (ChainCategory.tail C x)

  indexed-category-indexed-functor
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : IndexedCategory C)
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → IndexedFunctor
      (indexed-category-tail C' x)
      (indexed-category-tail C' y)
      (ChainCategory.chain-functor C f)

  indexed-category-indexed-functor-identity
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : IndexedCategory C)
    → (x : ChainCategory.Object C)
    → IndexedFunctorIdentity
      (indexed-category-indexed-functor C' (ChainCategory.identity C x))

  indexed-category-indexed-functor-compose
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : IndexedCategory C)
    → {x y z : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C y z)
    → (g : ChainCategory.Arrow C x y)
    → IndexedFunctorCompose
      (indexed-category-indexed-functor C' f)
      (indexed-category-indexed-functor C' g)
      (indexed-category-indexed-functor C' (ChainCategory.compose C f g))

  -- #### IndexedFunctor

  indexed-functor₀
    : {C D : ChainCategory zero}
    → {C' : IndexedCategory C}
    → {D' : IndexedCategory D}
    → {F : ChainFunctor C D}
    → IndexedFunctor C' D' F
    → Functor
      (indexed-category₀ C')
      (indexed-category₀ D')

  indexed-functor-tail
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → {D' : IndexedCategory D}
    → {F : ChainFunctor C D}
    → IndexedFunctor C' D' F
    → (x : ChainCategory.Object C)
    → IndexedFunctor
      (indexed-category-tail C' x)
      (indexed-category-tail D' (ChainFunctor.base F x))
      (ChainFunctor.tail F x)

  indexed-functor-indexed-functor-square
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → {D' : IndexedCategory D}
    → {F : ChainFunctor C D}
    → (F' : IndexedFunctor C' D' F)
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → IndexedFunctorSquare
      (indexed-category-indexed-functor C' f)
      (indexed-category-indexed-functor D' (ChainFunctor.map F f))
      (indexed-functor-tail F' x)
      (indexed-functor-tail F' y)

  -- #### IndexedFunctorIdentity

  indexed-functor-identity₀
    : {C : ChainCategory zero}
    → {C' : IndexedCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedFunctor C' C' F}
    → IndexedFunctorIdentity F'
    → FunctorIdentity
      (indexed-functor₀ F')

  indexed-functor-identity₀-eq
    : {A : Set}
    → {x₁ x₂ : A}
    → (C : A → ChainCategory zero)
    → (C' : (x : A) → IndexedCategory (C x))
    → {F : ChainFunctor (C x₁) (C x₂)}
    → {F' : IndexedFunctor (C' x₁) (C' x₂) F}
    → x₂ ≡ x₁
    → IndexedFunctorIdentity F'
    → FunctorIdentity
      (indexed-functor₀ F')

  indexed-functor-identity-head
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedFunctor C' C' F}
    → IndexedFunctorIdentity F'
    → FunctorIdentity
      (ChainFunctor.head F)

  indexed-functor-identity-base
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedFunctor C' C' F}
    → IndexedFunctorIdentity F'
    → (x : ChainCategory.Object C)
    → ChainFunctor.base F x ≡ x

  indexed-functor-identity-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedFunctor C' C' F}
    → IndexedFunctorIdentity F'
    → (x : ChainCategory.Object C)
    → IndexedFunctorIdentity
      (indexed-functor-tail F' x)

  -- #### IndexedFunctorCompose
  
  indexed-functor-compose₀
    : {C D E : ChainCategory zero}
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
    → FunctorCompose
      (indexed-functor₀ F')
      (indexed-functor₀ G')
      (indexed-functor₀ H')

  indexed-functor-compose₀-eq
    : {A : Set}
    → {x₁ x₂ : A}
    → {C D : ChainCategory zero}
    → (E : A → ChainCategory zero)
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
    → FunctorCompose
      (indexed-functor₀ F')
      (indexed-functor₀ G')
      (indexed-functor₀ H')

  indexed-functor-compose-head
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
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
    → FunctorCompose
      (ChainFunctor.head F)
      (ChainFunctor.head G)
      (ChainFunctor.head H)

  indexed-functor-compose-base
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
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
    → (x : ChainCategory.Object C)
    → ChainFunctor.base H x ≡ ChainFunctor.base F (ChainFunctor.base G x)

  indexed-functor-compose-tail
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
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
    → (x : ChainCategory.Object C)
    → IndexedFunctorCompose
      (indexed-functor-tail F' (ChainFunctor.base G x))
      (indexed-functor-tail G' x)
      (indexed-functor-tail H' x)

  -- #### IndexedFunctorSquare

  indexed-functor-square₀
    : {C₁ C₂ D₁ D₂ : ChainCategory zero}
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
    → FunctorSquare
      (indexed-functor₀ F')
      (indexed-functor₀ G')
      (indexed-functor₀ H₁')
      (indexed-functor₀ H₂')

  indexed-functor-square₀-eq
    : {A : Set}
    → {x₁ x₂ : A}
    → {C₁ C₂ D₁ : ChainCategory zero}
    → (D₂ : A → ChainCategory zero)
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
    → FunctorSquare
      (indexed-functor₀ F')
      (indexed-functor₀ G')
      (indexed-functor₀ H₁')
      (indexed-functor₀ H₂')

  indexed-functor-square-head
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
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
    → FunctorSquare
      (ChainFunctor.head F)
      (ChainFunctor.head G)
      (ChainFunctor.head H₁)
      (ChainFunctor.head H₂)

  indexed-functor-square-base
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
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
    → (x₁ : ChainCategory.Object C₁)
    → ChainFunctor.base H₂ (ChainFunctor.base F x₁)
      ≡ ChainFunctor.base G (ChainFunctor.base H₁ x₁)

  indexed-functor-square-tail
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
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
    → (x₁ : ChainCategory.Object C₁)
    → IndexedFunctorSquare
      (indexed-functor-tail F' x₁)
      (indexed-functor-tail G' (ChainFunctor.base H₁ x₁))
      (indexed-functor-tail H₁' x₁)
      (indexed-functor-tail H₂' (ChainFunctor.base F x₁))

  -- ### Definitions
  
  -- #### IndexedCategory
  
  data IndexedCategory where
  
    nil
      : {C : ChainCategory zero}
      → Category
      → IndexedCategory C

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → (C' : (x : ChainCategory.Object C)
        → IndexedCategory
          (ChainCategory.tail C x))
      → (F : {x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → IndexedFunctor (C' x) (C' y)
          (ChainCategory.chain-functor C f))
      → ((x : ChainCategory.Object C)
        → IndexedFunctorIdentity
          (F (ChainCategory.identity C x)))
      → ({x y z : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C y z)
        → (g : ChainCategory.Arrow C x y)
        → IndexedFunctorCompose (F f) (F g)
          (F (ChainCategory.compose C f g)))
      → IndexedCategory C
  
  indexed-category₀ (nil C')
    = C'

  indexed-category-tail (cons C' _ _ _)
    = C'

  indexed-category-indexed-functor (cons _ F _ _)
    = F

  indexed-category-indexed-functor-identity (cons _ _ p _)
    = p

  indexed-category-indexed-functor-compose (cons _ _ _ p)
    = p

  -- #### IndexedFunctor
  
  data IndexedFunctor where
  
    nil
      : {C D : ChainCategory zero}
      → {C' : IndexedCategory C}
      → {D' : IndexedCategory D}
      → {F : ChainFunctor C D}
      → Functor
        (indexed-category₀ C')
        (indexed-category₀ D')
      → IndexedFunctor C' D' F

    cons
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → {C' : IndexedCategory C}
      → {D' : IndexedCategory D}
      → {F : ChainFunctor C D}
      → (F' : (x : ChainCategory.Object C)
        → IndexedFunctor
          (indexed-category-tail C' x)
          (indexed-category-tail D' (ChainFunctor.base F x))
          (ChainFunctor.tail F x))
      → ({x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → IndexedFunctorSquare
          (indexed-category-indexed-functor C' f)
          (indexed-category-indexed-functor D' (ChainFunctor.map F f))
          (F' x)
          (F' y))
      → IndexedFunctor C' D' F
  
  indexed-functor₀ (nil F')
    = F'

  indexed-functor-tail (cons F' _)
    = F'

  indexed-functor-indexed-functor-square (cons _ s)
    = s

  -- #### IndexedFunctorIdentity
  
  data IndexedFunctorIdentity where
  
    nil
      : {C : ChainCategory zero}
      → {C' : IndexedCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedFunctor C' C' F}
      → FunctorIdentity
        (indexed-functor₀ F')
      → IndexedFunctorIdentity F'

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedFunctor C' C' F}
      → FunctorIdentity
        (ChainFunctor.head F)
      → ((x : ChainCategory.Object C)
        → IndexedFunctorIdentity
          (indexed-functor-tail F' x))
      → IndexedFunctorIdentity F'

  indexed-functor-identity₀ (nil p)
    = p

  indexed-functor-identity₀-eq _ _ refl
    = indexed-functor-identity₀

  indexed-functor-identity-head (cons p _)
    = p

  indexed-functor-identity-base p
    = FunctorIdentity.base
      (indexed-functor-identity-head p)

  indexed-functor-identity-tail (cons _ p)
    = p

  -- #### IndexedFunctorCompose
  
  data IndexedFunctorCompose where
  
    nil
      : {C D E : ChainCategory zero}
      → {C' : IndexedCategory C}
      → {D' : IndexedCategory D}
      → {E' : IndexedCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : IndexedFunctor D' E' F}
      → {G' : IndexedFunctor C' D' G}
      → {H' : IndexedFunctor C' E' H}
      → FunctorCompose
        (indexed-functor₀ F')
        (indexed-functor₀ G')
        (indexed-functor₀ H')
      → IndexedFunctorCompose F' G' H'

    cons
      : {n : ℕ}
      → {C D E : ChainCategory (suc n)}
      → {C' : IndexedCategory C}
      → {D' : IndexedCategory D}
      → {E' : IndexedCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : IndexedFunctor D' E' F}
      → {G' : IndexedFunctor C' D' G}
      → {H' : IndexedFunctor C' E' H}
      → FunctorCompose
        (ChainFunctor.head F)
        (ChainFunctor.head G)
        (ChainFunctor.head H)
      → ((x : ChainCategory.Object C)
        → IndexedFunctorCompose
          (indexed-functor-tail F' (ChainFunctor.base G x))
          (indexed-functor-tail G' x)
          (indexed-functor-tail H' x))
      → IndexedFunctorCompose F' G' H'

  indexed-functor-compose₀ (nil p)
    = p

  indexed-functor-compose₀-eq _ _ refl
    = indexed-functor-compose₀

  indexed-functor-compose-head (cons p _)
    = p

  indexed-functor-compose-base p
    = FunctorCompose.base
      (indexed-functor-compose-head p)

  indexed-functor-compose-tail (cons _ p)
    = p

  -- #### IndexedFunctorSquare
  
  data IndexedFunctorSquare where
  
    nil
      : {C₁ C₂ D₁ D₂ : ChainCategory zero}
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
      → FunctorSquare
        (indexed-functor₀ F')
        (indexed-functor₀ G')
        (indexed-functor₀ H₁')
        (indexed-functor₀ H₂')
      → IndexedFunctorSquare F' G' H₁' H₂'

    cons
      : {n : ℕ}
      → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
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
      → FunctorSquare
        (ChainFunctor.head F)
        (ChainFunctor.head G)
        (ChainFunctor.head H₁)
        (ChainFunctor.head H₂)
      → ((x₁ : ChainCategory.Object C₁)
        → IndexedFunctorSquare
          (indexed-functor-tail F' x₁)
          (indexed-functor-tail G' (ChainFunctor.base H₁ x₁))
          (indexed-functor-tail H₁' x₁)
          (indexed-functor-tail H₂' (ChainFunctor.base F x₁)))
      → IndexedFunctorSquare F' G' H₁' H₂'

  indexed-functor-square₀ (nil s)
    = s

  indexed-functor-square₀-eq _ _ refl
    = indexed-functor-square₀

  indexed-functor-square-head (cons s _)
    = s

  indexed-functor-square-base s
    = FunctorSquare.base
      (indexed-functor-square-head s)

  indexed-functor-square-tail (cons _ s)
    = s

  -- ### Destruction

  -- #### IndexedCategory

  module _
    {C : ChainCategory (suc zero)}
    where

    module IndexedCategory₁
      (C' : IndexedCategory C)
      where

      category
        : Category.Object (ChainCategory.head C)
        → Category
      category x
        = indexed-category₀
          (indexed-category-tail C' x)

      functor
        : {x y : Category.Object (ChainCategory.head C)}
        → Category.Arrow (ChainCategory.head C) x y
        → Functor
          (category x)
          (category y)
      functor f
        = indexed-functor₀
          (indexed-category-indexed-functor C' f)

      abstract

        functor-identity
          : (x : Category.Object (ChainCategory.head C))
          → FunctorIdentity
            (functor (Category.identity (ChainCategory.head C) x))
        functor-identity x
          = indexed-functor-identity₀
            (indexed-category-indexed-functor-identity C' x)

        functor-compose
          : {x y z : Category.Object (ChainCategory.head C)}
          → (f : Category.Arrow (ChainCategory.head C) y z)
          → (g : Category.Arrow (ChainCategory.head C) x y)
          → FunctorCompose
            (functor f)
            (functor g)
            (functor (Category.compose (ChainCategory.head C) f g))
        functor-compose f g
          = indexed-functor-compose₀
            (indexed-category-indexed-functor-compose C' f g)

    indexed-category₁
      : IndexedCategory C
      → DependentCategory
        (ChainCategory.head C)
    indexed-category₁ C'
      = record {IndexedCategory₁ C'}

  -- #### IndexedFunctor

  module _
    {C D : ChainCategory (suc zero)}
    {C' : IndexedCategory C}
    {D' : IndexedCategory D}
    {F : ChainFunctor C D}
    where

    module IndexedFunctor₁
      (F' : IndexedFunctor C' D' F)
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
          (DependentCategory.category (indexed-category₁ C') x)
          (DependentCategory.category (indexed-category₁ D') (base x))
      functor' x
        = indexed-functor₀
          (indexed-functor-tail F' x)

      abstract

        functor-square
          : {x y : Category.Object (ChainCategory.head C)}
          → (f : Category.Arrow (ChainCategory.head C) x y)
          → FunctorSquare
            (DependentCategory.functor (indexed-category₁ C') f)
            (DependentCategory.functor (indexed-category₁ D') (map f))
            (functor' x)
            (functor' y)
        functor-square f
          = indexed-functor-square₀
            (indexed-functor-indexed-functor-square F' f)

    indexed-functor₁
      : IndexedFunctor C' D' F
      → DependentFunctor
        (indexed-category₁ C')
        (indexed-category₁ D')
    indexed-functor₁ F'
      = record {IndexedFunctor₁ F'}

  -- #### IndexedFunctorIdentity

  module _
    {C : ChainCategory (suc zero)}
    {C' : IndexedCategory C}
    {F : ChainFunctor C C}
    {F' : IndexedFunctor C' C' F}
    where

    module IndexedFunctorIdentity₁
      (p : IndexedFunctorIdentity F')
      where

      functor
        : FunctorIdentity
          (DependentFunctor.functor (indexed-functor₁ F'))
      functor
        = indexed-functor-identity-head p
          
      functor'
        : (x : Category.Object (ChainCategory.head C))
        → FunctorIdentity
          (DependentFunctor.functor' (indexed-functor₁ F') x)
      functor' x
        = indexed-functor-identity₀-eq
          (ChainCategory.tail C)
          (indexed-category-tail C')
          (indexed-functor-identity-base p x)
          (indexed-functor-identity-tail p x)

    indexed-functor-identity₁
      : IndexedFunctorIdentity F'
      → DependentFunctorIdentity
        (indexed-functor₁ F')
    indexed-functor-identity₁ p
      = record {IndexedFunctorIdentity₁ p}

  -- #### IndexedFunctorCompose

  module _
    {C D E : ChainCategory (suc zero)}
    {C' : IndexedCategory C}
    {D' : IndexedCategory D}
    {E' : IndexedCategory E}
    {F : ChainFunctor D E}
    {G : ChainFunctor C D}
    {H : ChainFunctor C E}
    {F' : IndexedFunctor D' E' F}
    {G' : IndexedFunctor C' D' G}
    {H' : IndexedFunctor C' E' H}
    where

    module IndexedFunctorCompose₁
      (p : IndexedFunctorCompose F' G' H')
      where

      functor
        : FunctorCompose
          (DependentFunctor.functor (indexed-functor₁ F'))
          (DependentFunctor.functor (indexed-functor₁ G'))
          (DependentFunctor.functor (indexed-functor₁ H'))
      functor
        = indexed-functor-compose-head p

      functor'
        : (x : Category.Object (ChainCategory.head C))
        → FunctorCompose
          (DependentFunctor.functor' (indexed-functor₁ F')
            (DependentFunctor.base (indexed-functor₁ G') x))
          (DependentFunctor.functor' (indexed-functor₁ G') x)
          (DependentFunctor.functor' (indexed-functor₁ H') x)
      functor' x
        = indexed-functor-compose₀-eq
          (ChainCategory.tail E)
          (indexed-category-tail E')
          (indexed-functor-compose-base p x)
          (indexed-functor-compose-tail p x)

    indexed-functor-compose₁
      : IndexedFunctorCompose F' G' H'
      → DependentFunctorCompose
        (indexed-functor₁ F')
        (indexed-functor₁ G')
        (indexed-functor₁ H')
    indexed-functor-compose₁ p
      = record {IndexedFunctorCompose₁ p}

  -- #### IndexedFunctorSquare

  module _
    {C₁ C₂ D₁ D₂ : ChainCategory (suc zero)}
    {C₁' : IndexedCategory C₁}
    {C₂' : IndexedCategory C₂}
    {D₁' : IndexedCategory D₁}
    {D₂' : IndexedCategory D₂}
    {F : ChainFunctor C₁ C₂}
    {G : ChainFunctor D₁ D₂}
    {H₁ : ChainFunctor C₁ D₁}
    {H₂ : ChainFunctor C₂ D₂}
    {F' : IndexedFunctor C₁' C₂' F}
    {G' : IndexedFunctor D₁' D₂' G}
    {H₁' : IndexedFunctor C₁' D₁' H₁}
    {H₂' : IndexedFunctor C₂' D₂' H₂}
    where

    module IndexedFunctorSquare₁
      (s : IndexedFunctorSquare F' G' H₁' H₂')
      where

      functor
        : FunctorSquare
          (DependentFunctor.functor (indexed-functor₁ F'))
          (DependentFunctor.functor (indexed-functor₁ G'))
          (DependentFunctor.functor (indexed-functor₁ H₁'))
          (DependentFunctor.functor (indexed-functor₁ H₂'))
      functor
        = indexed-functor-square-head s

      functor'
        : (x₁ : Category.Object (ChainCategory.head C₁))
        → FunctorSquare
          (DependentFunctor.functor' (indexed-functor₁ F') x₁)
          (DependentFunctor.functor' (indexed-functor₁ G')
            (DependentFunctor.base (indexed-functor₁ H₁') x₁))
          (DependentFunctor.functor' (indexed-functor₁ H₁') x₁)
          (DependentFunctor.functor' (indexed-functor₁ H₂')
            (DependentFunctor.base (indexed-functor₁ F') x₁))
      functor' x₁
        = indexed-functor-square₀-eq
          (ChainCategory.tail D₂)
          (indexed-category-tail D₂')
          (indexed-functor-square-base s x₁)
          (indexed-functor-square-tail s x₁)

    indexed-functor-square₁
      : IndexedFunctorSquare F' G' H₁' H₂'
      → DependentFunctorSquare
        (indexed-functor₁ F')
        (indexed-functor₁ G')
        (indexed-functor₁ H₁')
        (indexed-functor₁ H₂')
    indexed-functor-square₁ s
      = record {IndexedFunctorSquare₁ s}

-- ## Modules

-- ### IndexedCategory

IndexedCategory
  : {n : ℕ}
  → ChainCategory n
  → Set₁
IndexedCategory
  = Internal.IndexedCategory

open Internal.IndexedCategory public

open Internal public
  using (indexed-category₀; indexed-category₁)

module IndexedCategory where

  open Internal public using () renaming
    ( indexed-category-tail
      to tail
    ; indexed-category-indexed-functor
      to indexed-functor
    ; indexed-category-indexed-functor-compose
      to indexed-functor-compose
    ; indexed-category-indexed-functor-identity
      to indexed-functor-identity
    )

-- ### IndexedFunctor

IndexedFunctor
  : {n : ℕ}
  → {C D : ChainCategory n}
  → IndexedCategory C
  → IndexedCategory D
  → ChainFunctor C D
  → Set
IndexedFunctor
  = Internal.IndexedFunctor
  
open Internal.IndexedFunctor public

open Internal public
  using (indexed-functor₀; indexed-functor₁)

module IndexedFunctor where

  open Internal public using () renaming
    ( indexed-functor-tail
      to tail
    ; indexed-functor-indexed-functor-square
      to indexed-functor-square
    )

-- ### IndexedFunctorIdentity

IndexedFunctorIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : IndexedCategory C₁}
  → {C₂' : IndexedCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → IndexedFunctor C₁' C₂' F
  → Set
IndexedFunctorIdentity
  = Internal.IndexedFunctorIdentity
  
open Internal.IndexedFunctorIdentity public

open Internal public
  using (indexed-functor-identity₀; indexed-functor-identity₁)

module IndexedFunctorIdentity where

  open Internal public using () renaming
    ( indexed-functor-identity-base
      to base
    ; indexed-functor-identity-head
      to head
    ; indexed-functor-identity-tail
      to tail
    )

-- ### IndexedFunctorCompose

IndexedFunctorCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → {C' : IndexedCategory C}
  → {D' : IndexedCategory D}
  → {E₁' : IndexedCategory E₁}
  → {E₂' : IndexedCategory E₂}
  → {F : ChainFunctor D E₁}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E₂}
  → IndexedFunctor D' E₁' F
  → IndexedFunctor C' D' G
  → IndexedFunctor C' E₂' H
  → Set
IndexedFunctorCompose
  = Internal.IndexedFunctorCompose
  
open Internal.IndexedFunctorCompose public

open Internal public
  using (indexed-functor-compose₀; indexed-functor-compose₁)

module IndexedFunctorCompose where

  open Internal public using () renaming
    ( indexed-functor-compose-base
      to base
    ; indexed-functor-compose-head
      to head
    ; indexed-functor-compose-tail
      to tail
    )

-- ### IndexedFunctorSquare

IndexedFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
  → {C₁' : IndexedCategory C₁}
  → {C₂' : IndexedCategory C₂}
  → {D₁' : IndexedCategory D₁}
  → {D₂' : IndexedCategory D₂}
  → {D₃' : IndexedCategory D₃}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₃}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → IndexedFunctor C₁' C₂' F
  → IndexedFunctor D₁' D₃' G
  → IndexedFunctor C₁' D₁' H₁
  → IndexedFunctor C₂' D₂' H₂
  → Set
IndexedFunctorSquare
  = Internal.IndexedFunctorSquare
  
open Internal.IndexedFunctorSquare public

open Internal public
  using (indexed-functor-square₀; indexed-functor-square₁)

module IndexedFunctorSquare where

  open Internal public using () renaming
    ( indexed-functor-square-base
      to base
    ; indexed-functor-square-head
      to head
    ; indexed-functor-square-tail
      to tail
    )

