module Prover.Category.Indexed.Simple where

open import Prover.Category
  using (FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Function
  using (Function; FunctionCompose; FunctionIdentity; FunctionSquare)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types
  
  -- #### IndexedSimpleCategory
  
  data IndexedSimpleCategory
    : {n : ℕ}
    → ChainCategory n
    → Set₁
  
  -- #### IndexedSimpleFunctor
  
  data IndexedSimpleFunctor
    : {n : ℕ}
    → {C D : ChainCategory n}
    → IndexedSimpleCategory C
    → IndexedSimpleCategory D
    → ChainFunctor C D
    → Set
  
  -- #### IndexedSimpleFunctorIdentity
  
  data IndexedSimpleFunctorIdentity
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory n}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → IndexedSimpleFunctor C₁' C₂' F
    → Set
  
  -- #### IndexedSimpleFunctorCompose
  
  data IndexedSimpleFunctorCompose
    : {n : ℕ}
    → {C D E₁ E₂ : ChainCategory n}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {E₁' : IndexedSimpleCategory E₁}
    → {E₂' : IndexedSimpleCategory E₂}
    → {F : ChainFunctor D E₁}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E₂}
    → IndexedSimpleFunctor D' E₁' F
    → IndexedSimpleFunctor C' D' G
    → IndexedSimpleFunctor C' E₂' H
    → Set
  
  -- #### IndexedSimpleFunctorSquare
  
  data IndexedSimpleFunctorSquare
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {D₁' : IndexedSimpleCategory D₁}
    → {D₂' : IndexedSimpleCategory D₂}
    → {D₃' : IndexedSimpleCategory D₃}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₃}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → IndexedSimpleFunctor C₁' C₂' F
    → IndexedSimpleFunctor D₁' D₃' G
    → IndexedSimpleFunctor C₁' D₁' H₁
    → IndexedSimpleFunctor C₂' D₂' H₂
    → Set
    
  -- ### Interface

  -- #### IndexedSimpleCategory

  indexed-simple-category₀
    : {C : ChainCategory zero}
    → IndexedSimpleCategory C
    → Set

  indexed-simple-category-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSimpleCategory C
    → (x : ChainCategory.Object C)
    → IndexedSimpleCategory
      (ChainCategory.tail C x)
  
  indexed-simple-category-indexed-simple-functor
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : IndexedSimpleCategory C)
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → IndexedSimpleFunctor
      (indexed-simple-category-tail C' x)
      (indexed-simple-category-tail C' y)
      (ChainCategory.chain-functor C f)

  indexed-simple-category-indexed-simple-functor-identity
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : IndexedSimpleCategory C)
    → (x : ChainCategory.Object C)
    → IndexedSimpleFunctorIdentity
      (indexed-simple-category-indexed-simple-functor C'
        (ChainCategory.identity C x))

  indexed-simple-category-indexed-simple-functor-compose
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : IndexedSimpleCategory C)
    → {x y z : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C y z)
    → (g : ChainCategory.Arrow C x y)
    → IndexedSimpleFunctorCompose
      (indexed-simple-category-indexed-simple-functor C' f)
      (indexed-simple-category-indexed-simple-functor C' g)
      (indexed-simple-category-indexed-simple-functor C'
        (ChainCategory.compose C f g))

  -- #### IndexedSimpleFunctor

  indexed-simple-functor₀
    : {C D : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {F : ChainFunctor C D}
    → IndexedSimpleFunctor C' D' F
    → Function
      (indexed-simple-category₀ C')
      (indexed-simple-category₀ D')

  indexed-simple-functor-tail
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {F : ChainFunctor C D}
    → IndexedSimpleFunctor C' D' F
    → (x : ChainCategory.Object C)
    → IndexedSimpleFunctor
      (indexed-simple-category-tail C' x)
      (indexed-simple-category-tail D' (ChainFunctor.base F x))
      (ChainFunctor.tail F x)

  indexed-simple-functor-indexed-simple-functor-square
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {F : ChainFunctor C D}
    → (F' : IndexedSimpleFunctor C' D' F)
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → IndexedSimpleFunctorSquare
      (indexed-simple-category-indexed-simple-functor C' f)
      (indexed-simple-category-indexed-simple-functor D' (ChainFunctor.map F f))
      (indexed-simple-functor-tail F' x)
      (indexed-simple-functor-tail F' y)

  -- #### IndexedSimpleFunctorIdentity

  indexed-simple-functor-identity₀
    : {C : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedSimpleFunctor C' C' F}
    → IndexedSimpleFunctorIdentity F'
    → FunctionIdentity
      (indexed-simple-functor₀ F')

  indexed-simple-functor-identity-head
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedSimpleFunctor C' C' F}
    → IndexedSimpleFunctorIdentity F'
    → FunctorIdentity
      (ChainFunctor.head F)

  indexed-simple-functor-identity-base
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedSimpleFunctor C' C' F}
    → IndexedSimpleFunctorIdentity F'
    → (x : ChainCategory.Object C)
    → ChainFunctor.base F x ≡ x

  indexed-simple-functor-identity-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedSimpleFunctor C' C' F}
    → IndexedSimpleFunctorIdentity F'
    → (x : ChainCategory.Object C)
    → IndexedSimpleFunctorIdentity
      (indexed-simple-functor-tail F' x)

  -- #### IndexedSimpleFunctorCompose

  indexed-simple-functor-compose₀
    : {C D E : ChainCategory zero}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {E' : IndexedSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : IndexedSimpleFunctor D' E' F}
    → {G' : IndexedSimpleFunctor C' D' G}
    → {H' : IndexedSimpleFunctor C' E' H}
    → IndexedSimpleFunctorCompose F' G' H'
    → FunctionCompose
      (indexed-simple-functor₀ F')
      (indexed-simple-functor₀ G')
      (indexed-simple-functor₀ H')

  indexed-simple-functor-compose-head
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {E' : IndexedSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : IndexedSimpleFunctor D' E' F}
    → {G' : IndexedSimpleFunctor C' D' G}
    → {H' : IndexedSimpleFunctor C' E' H}
    → IndexedSimpleFunctorCompose F' G' H'
    → FunctorCompose
      (ChainFunctor.head F)
      (ChainFunctor.head G)
      (ChainFunctor.head H)

  indexed-simple-functor-compose-base
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {E' : IndexedSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : IndexedSimpleFunctor D' E' F}
    → {G' : IndexedSimpleFunctor C' D' G}
    → {H' : IndexedSimpleFunctor C' E' H}
    → IndexedSimpleFunctorCompose F' G' H'
    → (x : ChainCategory.Object C)
    → ChainFunctor.base H x ≡ ChainFunctor.base F (ChainFunctor.base G x)

  indexed-simple-functor-compose-tail
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : IndexedSimpleCategory C}
    → {D' : IndexedSimpleCategory D}
    → {E' : IndexedSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : IndexedSimpleFunctor D' E' F}
    → {G' : IndexedSimpleFunctor C' D' G}
    → {H' : IndexedSimpleFunctor C' E' H}
    → IndexedSimpleFunctorCompose F' G' H'
    → (x : ChainCategory.Object C)
    → IndexedSimpleFunctorCompose
      (indexed-simple-functor-tail F' (ChainFunctor.base G x))
      (indexed-simple-functor-tail G' x)
      (indexed-simple-functor-tail H' x)

  -- #### IndexedSimpleFunctorSquare

  indexed-simple-functor-square₀
    : {C₁ C₂ D₁ D₂ : ChainCategory zero}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {D₁' : IndexedSimpleCategory D₁}
    → {D₂' : IndexedSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : IndexedSimpleFunctor C₁' C₂' F}
    → {G' : IndexedSimpleFunctor D₁' D₂' G}
    → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
    → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
    → IndexedSimpleFunctorSquare F' G' H₁' H₂'
    → FunctionSquare
      (indexed-simple-functor₀ F')
      (indexed-simple-functor₀ G')
      (indexed-simple-functor₀ H₁')
      (indexed-simple-functor₀ H₂')

  indexed-simple-functor-square-head
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {D₁' : IndexedSimpleCategory D₁}
    → {D₂' : IndexedSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : IndexedSimpleFunctor C₁' C₂' F}
    → {G' : IndexedSimpleFunctor D₁' D₂' G}
    → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
    → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
    → IndexedSimpleFunctorSquare F' G' H₁' H₂'
    → FunctorSquare
      (ChainFunctor.head F)
      (ChainFunctor.head G)
      (ChainFunctor.head H₁)
      (ChainFunctor.head H₂)

  indexed-simple-functor-square-base
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {D₁' : IndexedSimpleCategory D₁}
    → {D₂' : IndexedSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : IndexedSimpleFunctor C₁' C₂' F}
    → {G' : IndexedSimpleFunctor D₁' D₂' G}
    → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
    → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
    → IndexedSimpleFunctorSquare F' G' H₁' H₂'
    → (x₁ : ChainCategory.Object C₁)
    → ChainFunctor.base H₂ (ChainFunctor.base F x₁)
      ≡ ChainFunctor.base G (ChainFunctor.base H₁ x₁)

  indexed-simple-functor-square-tail
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : IndexedSimpleCategory C₁}
    → {C₂' : IndexedSimpleCategory C₂}
    → {D₁' : IndexedSimpleCategory D₁}
    → {D₂' : IndexedSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : IndexedSimpleFunctor C₁' C₂' F}
    → {G' : IndexedSimpleFunctor D₁' D₂' G}
    → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
    → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
    → IndexedSimpleFunctorSquare F' G' H₁' H₂'
    → (x₁ : ChainCategory.Object C₁)
    → IndexedSimpleFunctorSquare
      (indexed-simple-functor-tail F' x₁)
      (indexed-simple-functor-tail G' (ChainFunctor.base H₁ x₁))
      (indexed-simple-functor-tail H₁' x₁)
      (indexed-simple-functor-tail H₂' (ChainFunctor.base F x₁))

  -- ### Definitions
  
  -- #### IndexedSimpleCategory
  
  data IndexedSimpleCategory where
  
    nil
      : {C : ChainCategory zero}
      → Set
      → IndexedSimpleCategory C

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → (C' : (x : ChainCategory.Object C)
        → IndexedSimpleCategory
          (ChainCategory.tail C x))
      → (F : {x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → IndexedSimpleFunctor (C' x) (C' y)
          (ChainCategory.chain-functor C f))
      → ((x : ChainCategory.Object C)
        → IndexedSimpleFunctorIdentity
          (F (ChainCategory.identity C x)))
      → ({x y z : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C y z)
        → (g : ChainCategory.Arrow C x y)
        → IndexedSimpleFunctorCompose (F f) (F g)
          (F (ChainCategory.compose C f g)))
      → IndexedSimpleCategory C

  indexed-simple-category₀ (nil A)
    = A

  indexed-simple-category-tail (cons C' _ _ _)
    = C'

  indexed-simple-category-indexed-simple-functor (cons _ F _ _)
    = F

  indexed-simple-category-indexed-simple-functor-identity (cons _ _ p _)
    = p

  indexed-simple-category-indexed-simple-functor-compose (cons _ _ _ p)
    = p

  -- #### IndexedSimpleFunctor
  
  data IndexedSimpleFunctor where
  
    nil
      : {C D : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {F : ChainFunctor C D}
      → Function
        (indexed-simple-category₀ C')
        (indexed-simple-category₀ D')
      → IndexedSimpleFunctor C' D' F

    cons
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {F : ChainFunctor C D}
      → (F' : (x : ChainCategory.Object C)
        → IndexedSimpleFunctor
          (indexed-simple-category-tail C' x)
          (indexed-simple-category-tail D' (ChainFunctor.base F x))
          (ChainFunctor.tail F x))
      → ({x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → IndexedSimpleFunctorSquare
          (indexed-simple-category-indexed-simple-functor C' f)
          (indexed-simple-category-indexed-simple-functor D'
            (ChainFunctor.map F f))
          (F' x)
          (F' y))
      → IndexedSimpleFunctor C' D' F

  indexed-simple-functor₀ (nil f)
    = f

  indexed-simple-functor-tail (cons F' _)
    = F'

  indexed-simple-functor-indexed-simple-functor-square (cons _ s)
    = s

  -- #### IndexedSimpleFunctorIdentity
  
  data IndexedSimpleFunctorIdentity where
  
    nil
      : {C : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedSimpleFunctor C' C' F}
      → FunctionIdentity
        (indexed-simple-functor₀ F')
      → IndexedSimpleFunctorIdentity F'

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedSimpleFunctor C' C' F}
      → FunctorIdentity
        (ChainFunctor.head F)
      → ((x : ChainCategory.Object C)
        → IndexedSimpleFunctorIdentity
          (indexed-simple-functor-tail F' x))
      → IndexedSimpleFunctorIdentity F'

  indexed-simple-functor-identity₀ (nil p)
    = p

  indexed-simple-functor-identity-head (cons p _)
    = p

  indexed-simple-functor-identity-base p
    = FunctorIdentity.base
      (indexed-simple-functor-identity-head p)

  indexed-simple-functor-identity-tail (cons _ p)
    = p

  -- #### IndexedSimpleFunctorCompose
  
  data IndexedSimpleFunctorCompose where
  
    nil
      : {C D E : ChainCategory zero}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {E' : IndexedSimpleCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : IndexedSimpleFunctor D' E' F}
      → {G' : IndexedSimpleFunctor C' D' G}
      → {H' : IndexedSimpleFunctor C' E' H}
      → FunctionCompose
        (indexed-simple-functor₀ F')
        (indexed-simple-functor₀ G')
        (indexed-simple-functor₀ H')
      → IndexedSimpleFunctorCompose F' G' H'

    cons
      : {n : ℕ}
      → {C D E : ChainCategory (suc n)}
      → {C' : IndexedSimpleCategory C}
      → {D' : IndexedSimpleCategory D}
      → {E' : IndexedSimpleCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : IndexedSimpleFunctor D' E' F}
      → {G' : IndexedSimpleFunctor C' D' G}
      → {H' : IndexedSimpleFunctor C' E' H}
      → FunctorCompose
        (ChainFunctor.head F)
        (ChainFunctor.head G)
        (ChainFunctor.head H)
      → ((x : ChainCategory.Object C)
        → IndexedSimpleFunctorCompose
          (indexed-simple-functor-tail F' (ChainFunctor.base G x))
          (indexed-simple-functor-tail G' x)
          (indexed-simple-functor-tail H' x))
      → IndexedSimpleFunctorCompose F' G' H'

  indexed-simple-functor-compose₀ (nil p)
    = p

  indexed-simple-functor-compose-head (cons p _)
    = p

  indexed-simple-functor-compose-base p
    = FunctorCompose.base
      (indexed-simple-functor-compose-head p)

  indexed-simple-functor-compose-tail (cons _ p)
    = p

  -- #### IndexedSimpleFunctorSquare
  
  data IndexedSimpleFunctorSquare where
  
    nil
      : {C₁ C₂ D₁ D₂ : ChainCategory zero}
      → {C₁' : IndexedSimpleCategory C₁}
      → {C₂' : IndexedSimpleCategory C₂}
      → {D₁' : IndexedSimpleCategory D₁}
      → {D₂' : IndexedSimpleCategory D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : IndexedSimpleFunctor C₁' C₂' F}
      → {G' : IndexedSimpleFunctor D₁' D₂' G}
      → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
      → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
      → FunctionSquare
        (indexed-simple-functor₀ F')
        (indexed-simple-functor₀ G')
        (indexed-simple-functor₀ H₁')
        (indexed-simple-functor₀ H₂')
      → IndexedSimpleFunctorSquare F' G' H₁' H₂'

    cons
      : {n : ℕ}
      → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
      → {C₁' : IndexedSimpleCategory C₁}
      → {C₂' : IndexedSimpleCategory C₂}
      → {D₁' : IndexedSimpleCategory D₁}
      → {D₂' : IndexedSimpleCategory D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : IndexedSimpleFunctor C₁' C₂' F}
      → {G' : IndexedSimpleFunctor D₁' D₂' G}
      → {H₁' : IndexedSimpleFunctor C₁' D₁' H₁}
      → {H₂' : IndexedSimpleFunctor C₂' D₂' H₂}
      → FunctorSquare
        (ChainFunctor.head F)
        (ChainFunctor.head G)
        (ChainFunctor.head H₁)
        (ChainFunctor.head H₂)
      → ((x₁ : ChainCategory.Object C₁)
        → IndexedSimpleFunctorSquare
          (indexed-simple-functor-tail F' x₁)
          (indexed-simple-functor-tail G' (ChainFunctor.base H₁ x₁))
          (indexed-simple-functor-tail H₁' x₁)
          (indexed-simple-functor-tail H₂' (ChainFunctor.base F x₁)))
      → IndexedSimpleFunctorSquare F' G' H₁' H₂'

  indexed-simple-functor-square₀ (nil s)
    = s

  indexed-simple-functor-square-head (cons s _)
    = s

  indexed-simple-functor-square-base s
    = FunctorSquare.base
      (indexed-simple-functor-square-head s)

  indexed-simple-functor-square-tail (cons _ s)
    = s

-- ## Modules

-- ### IndexedSimpleCategory

IndexedSimpleCategory
  : {n : ℕ}
  → ChainCategory n
  → Set₁
IndexedSimpleCategory
  = Internal.IndexedSimpleCategory

open Internal.IndexedSimpleCategory public

open Internal public
  using (indexed-simple-category₀)

module IndexedSimpleCategory where

  open Internal public using () renaming
    ( indexed-simple-category-indexed-simple-functor
      to indexed-simple-functor
    ; indexed-simple-category-indexed-simple-functor-compose
      to indexed-simple-functor-compose
    ; indexed-simple-category-indexed-simple-functor-identity
      to indexed-simple-functor-identity
    ; indexed-simple-category-tail
      to tail
    )

-- ### IndexedSimpleFunctor

IndexedSimpleFunctor
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → IndexedSimpleCategory C₁
  → IndexedSimpleCategory C₂
  → ChainFunctor C₁ C₂
  → Set
IndexedSimpleFunctor
  = Internal.IndexedSimpleFunctor

open Internal.IndexedSimpleFunctor public

open Internal public
  using (indexed-simple-functor₀)

module IndexedSimpleFunctor where

  open Internal public using () renaming
    ( indexed-simple-functor-indexed-simple-functor-square
      to indexed-simple-functor-square
    ; indexed-simple-functor-tail
      to tail
    )

-- ### IndexedSimpleFunctorIdentity

IndexedSimpleFunctorIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : IndexedSimpleCategory C₁}
  → {C₂' : IndexedSimpleCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → IndexedSimpleFunctor C₁' C₂' F
  → Set
IndexedSimpleFunctorIdentity
  = Internal.IndexedSimpleFunctorIdentity

open Internal.IndexedSimpleFunctorIdentity public

open Internal public
  using (indexed-simple-functor-identity₀)

module IndexedSimpleFunctorIdentity where

  open Internal public using () renaming
    ( indexed-simple-functor-identity-base
      to base
    ; indexed-simple-functor-identity-head
      to head
    ; indexed-simple-functor-identity-tail
      to tail
    )

-- ### IndexedSimpleFunctorCompose

IndexedSimpleFunctorCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → {D' : IndexedSimpleCategory D}
  → {E₁' : IndexedSimpleCategory E₁}
  → {E₂' : IndexedSimpleCategory E₂}
  → {F : ChainFunctor D E₁}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E₂}
  → IndexedSimpleFunctor D' E₁' F
  → IndexedSimpleFunctor C' D' G
  → IndexedSimpleFunctor C' E₂' H
  → Set
IndexedSimpleFunctorCompose
  = Internal.IndexedSimpleFunctorCompose

open Internal.IndexedSimpleFunctorCompose public

open Internal public
  using (indexed-simple-functor-compose₀)

module IndexedSimpleFunctorCompose where

  open Internal public using () renaming
    ( indexed-simple-functor-compose-base
      to base
    ; indexed-simple-functor-compose-head
      to head
    ; indexed-simple-functor-compose-tail
      to tail
    )

-- ### IndexedSimpleFunctorSquare

IndexedSimpleFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
  → {C₁' : IndexedSimpleCategory C₁}
  → {C₂' : IndexedSimpleCategory C₂}
  → {D₁' : IndexedSimpleCategory D₁}
  → {D₂' : IndexedSimpleCategory D₂}
  → {D₃' : IndexedSimpleCategory D₃}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₃}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → IndexedSimpleFunctor C₁' C₂' F
  → IndexedSimpleFunctor D₁' D₃' G
  → IndexedSimpleFunctor C₁' D₁' H₁
  → IndexedSimpleFunctor C₂' D₂' H₂
  → Set
IndexedSimpleFunctorSquare
  = Internal.IndexedSimpleFunctorSquare

open Internal.IndexedSimpleFunctorSquare public

open Internal public
  using (indexed-simple-functor-square₀)

module IndexedSimpleFunctorSquare where

  open Internal public using () renaming
    ( indexed-simple-functor-square-base
      to base
    ; indexed-simple-functor-square-head
      to head
    ; indexed-simple-functor-square-tail
      to tail
    )

