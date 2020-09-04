module Prover.Category.Dependent.Simple where

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
  
  -- #### DependentSimpleCategory
  
  data DependentSimpleCategory
    : {n : ℕ}
    → ChainCategory n
    → Set₁
  
  -- #### DependentSimpleFunctor
  
  data DependentSimpleFunctor
    : {n : ℕ}
    → {C D : ChainCategory n}
    → DependentSimpleCategory C
    → DependentSimpleCategory D
    → ChainFunctor C D
    → Set
  
  -- #### DependentSimpleFunctorIdentity
  
  data DependentSimpleFunctorIdentity
    : {n : ℕ}
    → {C₁ C₂ : ChainCategory n}
    → {C₁' : DependentSimpleCategory C₁}
    → {C₂' : DependentSimpleCategory C₂}
    → {F : ChainFunctor C₁ C₂}
    → DependentSimpleFunctor C₁' C₂' F
    → Set
  
  -- #### DependentSimpleFunctorCompose
  
  data DependentSimpleFunctorCompose
    : {n : ℕ}
    → {C D E₁ E₂ : ChainCategory n}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSimpleCategory D}
    → {E₁' : DependentSimpleCategory E₁}
    → {E₂' : DependentSimpleCategory E₂}
    → {F : ChainFunctor D E₁}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E₂}
    → DependentSimpleFunctor D' E₁' F
    → DependentSimpleFunctor C' D' G
    → DependentSimpleFunctor C' E₂' H
    → Set
  
  -- #### DependentSimpleFunctorSquare
  
  data DependentSimpleFunctorSquare
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
    → {C₁' : DependentSimpleCategory C₁}
    → {C₂' : DependentSimpleCategory C₂}
    → {D₁' : DependentSimpleCategory D₁}
    → {D₂' : DependentSimpleCategory D₂}
    → {D₃' : DependentSimpleCategory D₃}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₃}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → DependentSimpleFunctor C₁' C₂' F
    → DependentSimpleFunctor D₁' D₃' G
    → DependentSimpleFunctor C₁' D₁' H₁
    → DependentSimpleFunctor C₂' D₂' H₂
    → Set
    
  -- ### Interface

  -- #### DependentSimpleCategory

  dependent-simple-category₀
    : {C : ChainCategory zero}
    → DependentSimpleCategory C
    → Set

  dependent-simple-category-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → DependentSimpleCategory C
    → (x : ChainCategory.Object C)
    → DependentSimpleCategory
      (ChainCategory.tail C x)
  
  dependent-simple-category-dependent-simple-functor
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : DependentSimpleCategory C)
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → DependentSimpleFunctor
      (dependent-simple-category-tail C' x)
      (dependent-simple-category-tail C' y)
      (ChainCategory.chain-functor C f)

  dependent-simple-category-dependent-simple-functor-identity
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : DependentSimpleCategory C)
    → (x : ChainCategory.Object C)
    → DependentSimpleFunctorIdentity
      (dependent-simple-category-dependent-simple-functor C'
        (ChainCategory.identity C x))

  dependent-simple-category-dependent-simple-functor-compose
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → (C' : DependentSimpleCategory C)
    → {x y z : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C y z)
    → (g : ChainCategory.Arrow C x y)
    → DependentSimpleFunctorCompose
      (dependent-simple-category-dependent-simple-functor C' f)
      (dependent-simple-category-dependent-simple-functor C' g)
      (dependent-simple-category-dependent-simple-functor C'
        (ChainCategory.compose C f g))

  -- #### DependentSimpleFunctor

  dependent-simple-functor₀
    : {C D : ChainCategory zero}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSimpleCategory D}
    → {F : ChainFunctor C D}
    → DependentSimpleFunctor C' D' F
    → Function
      (dependent-simple-category₀ C')
      (dependent-simple-category₀ D')

  dependent-simple-functor-tail
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSimpleCategory D}
    → {F : ChainFunctor C D}
    → DependentSimpleFunctor C' D' F
    → (x : ChainCategory.Object C)
    → DependentSimpleFunctor
      (dependent-simple-category-tail C' x)
      (dependent-simple-category-tail D' (ChainFunctor.base F x))
      (ChainFunctor.tail F x)

  dependent-simple-functor-dependent-simple-functor-square
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSimpleCategory D}
    → {F : ChainFunctor C D}
    → (F' : DependentSimpleFunctor C' D' F)
    → {x y : ChainCategory.Object C}
    → (f : ChainCategory.Arrow C x y)
    → DependentSimpleFunctorSquare
      (dependent-simple-category-dependent-simple-functor C' f)
      (dependent-simple-category-dependent-simple-functor D'
        (ChainFunctor.map F f))
      (dependent-simple-functor-tail F' x)
      (dependent-simple-functor-tail F' y)

  -- #### DependentSimpleFunctorIdentity

  dependent-simple-functor-identity₀
    : {C : ChainCategory zero}
    → {C' : DependentSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : DependentSimpleFunctor C' C' F}
    → DependentSimpleFunctorIdentity F'
    → FunctionIdentity
      (dependent-simple-functor₀ F')

  dependent-simple-functor-identity-head
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : DependentSimpleFunctor C' C' F}
    → DependentSimpleFunctorIdentity F'
    → FunctorIdentity
      (ChainFunctor.head F)

  dependent-simple-functor-identity-base
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : DependentSimpleFunctor C' C' F}
    → DependentSimpleFunctorIdentity F'
    → (x : ChainCategory.Object C)
    → ChainFunctor.base F x ≡ x

  dependent-simple-functor-identity-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → {F : ChainFunctor C C}
    → {F' : DependentSimpleFunctor C' C' F}
    → DependentSimpleFunctorIdentity F'
    → (x : ChainCategory.Object C)
    → DependentSimpleFunctorIdentity
      (dependent-simple-functor-tail F' x)

  -- #### DependentSimpleFunctorCompose

  dependent-simple-functor-compose₀
    : {C D E : ChainCategory zero}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSimpleCategory D}
    → {E' : DependentSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : DependentSimpleFunctor D' E' F}
    → {G' : DependentSimpleFunctor C' D' G}
    → {H' : DependentSimpleFunctor C' E' H}
    → DependentSimpleFunctorCompose F' G' H'
    → FunctionCompose
      (dependent-simple-functor₀ F')
      (dependent-simple-functor₀ G')
      (dependent-simple-functor₀ H')

  dependent-simple-functor-compose-head
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSimpleCategory D}
    → {E' : DependentSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : DependentSimpleFunctor D' E' F}
    → {G' : DependentSimpleFunctor C' D' G}
    → {H' : DependentSimpleFunctor C' E' H}
    → DependentSimpleFunctorCompose F' G' H'
    → FunctorCompose
      (ChainFunctor.head F)
      (ChainFunctor.head G)
      (ChainFunctor.head H)

  dependent-simple-functor-compose-base
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSimpleCategory D}
    → {E' : DependentSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : DependentSimpleFunctor D' E' F}
    → {G' : DependentSimpleFunctor C' D' G}
    → {H' : DependentSimpleFunctor C' E' H}
    → DependentSimpleFunctorCompose F' G' H'
    → (x : ChainCategory.Object C)
    → ChainFunctor.base H x ≡ ChainFunctor.base F (ChainFunctor.base G x)

  dependent-simple-functor-compose-tail
    : {n : ℕ}
    → {C D E : ChainCategory (suc n)}
    → {C' : DependentSimpleCategory C}
    → {D' : DependentSimpleCategory D}
    → {E' : DependentSimpleCategory E}
    → {F : ChainFunctor D E}
    → {G : ChainFunctor C D}
    → {H : ChainFunctor C E}
    → {F' : DependentSimpleFunctor D' E' F}
    → {G' : DependentSimpleFunctor C' D' G}
    → {H' : DependentSimpleFunctor C' E' H}
    → DependentSimpleFunctorCompose F' G' H'
    → (x : ChainCategory.Object C)
    → DependentSimpleFunctorCompose
      (dependent-simple-functor-tail F' (ChainFunctor.base G x))
      (dependent-simple-functor-tail G' x)
      (dependent-simple-functor-tail H' x)

  -- #### DependentSimpleFunctorSquare

  dependent-simple-functor-square₀
    : {C₁ C₂ D₁ D₂ : ChainCategory zero}
    → {C₁' : DependentSimpleCategory C₁}
    → {C₂' : DependentSimpleCategory C₂}
    → {D₁' : DependentSimpleCategory D₁}
    → {D₂' : DependentSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : DependentSimpleFunctor C₁' C₂' F}
    → {G' : DependentSimpleFunctor D₁' D₂' G}
    → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
    → {H₂' : DependentSimpleFunctor C₂' D₂' H₂}
    → DependentSimpleFunctorSquare F' G' H₁' H₂'
    → FunctionSquare
      (dependent-simple-functor₀ F')
      (dependent-simple-functor₀ G')
      (dependent-simple-functor₀ H₁')
      (dependent-simple-functor₀ H₂')

  dependent-simple-functor-square-head
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : DependentSimpleCategory C₁}
    → {C₂' : DependentSimpleCategory C₂}
    → {D₁' : DependentSimpleCategory D₁}
    → {D₂' : DependentSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : DependentSimpleFunctor C₁' C₂' F}
    → {G' : DependentSimpleFunctor D₁' D₂' G}
    → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
    → {H₂' : DependentSimpleFunctor C₂' D₂' H₂}
    → DependentSimpleFunctorSquare F' G' H₁' H₂'
    → FunctorSquare
      (ChainFunctor.head F)
      (ChainFunctor.head G)
      (ChainFunctor.head H₁)
      (ChainFunctor.head H₂)

  dependent-simple-functor-square-base
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : DependentSimpleCategory C₁}
    → {C₂' : DependentSimpleCategory C₂}
    → {D₁' : DependentSimpleCategory D₁}
    → {D₂' : DependentSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : DependentSimpleFunctor C₁' C₂' F}
    → {G' : DependentSimpleFunctor D₁' D₂' G}
    → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
    → {H₂' : DependentSimpleFunctor C₂' D₂' H₂}
    → DependentSimpleFunctorSquare F' G' H₁' H₂'
    → (x₁ : ChainCategory.Object C₁)
    → ChainFunctor.base H₂ (ChainFunctor.base F x₁)
      ≡ ChainFunctor.base G (ChainFunctor.base H₁ x₁)

  dependent-simple-functor-square-tail
    : {n : ℕ}
    → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
    → {C₁' : DependentSimpleCategory C₁}
    → {C₂' : DependentSimpleCategory C₂}
    → {D₁' : DependentSimpleCategory D₁}
    → {D₂' : DependentSimpleCategory D₂}
    → {F : ChainFunctor C₁ C₂}
    → {G : ChainFunctor D₁ D₂}
    → {H₁ : ChainFunctor C₁ D₁}
    → {H₂ : ChainFunctor C₂ D₂}
    → {F' : DependentSimpleFunctor C₁' C₂' F}
    → {G' : DependentSimpleFunctor D₁' D₂' G}
    → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
    → {H₂' : DependentSimpleFunctor C₂' D₂' H₂}
    → DependentSimpleFunctorSquare F' G' H₁' H₂'
    → (x₁ : ChainCategory.Object C₁)
    → DependentSimpleFunctorSquare
      (dependent-simple-functor-tail F' x₁)
      (dependent-simple-functor-tail G' (ChainFunctor.base H₁ x₁))
      (dependent-simple-functor-tail H₁' x₁)
      (dependent-simple-functor-tail H₂' (ChainFunctor.base F x₁))

  -- ### Definitions
  
  -- #### DependentSimpleCategory
  
  data DependentSimpleCategory where
  
    nil
      : {C : ChainCategory zero}
      → Set
      → DependentSimpleCategory C

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → (C' : (x : ChainCategory.Object C)
        → DependentSimpleCategory
          (ChainCategory.tail C x))
      → (F : {x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → DependentSimpleFunctor (C' x) (C' y)
          (ChainCategory.chain-functor C f))
      → ((x : ChainCategory.Object C)
        → DependentSimpleFunctorIdentity
          (F (ChainCategory.identity C x)))
      → ({x y z : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C y z)
        → (g : ChainCategory.Arrow C x y)
        → DependentSimpleFunctorCompose (F f) (F g)
          (F (ChainCategory.compose C f g)))
      → DependentSimpleCategory C

  dependent-simple-category₀ (nil A)
    = A

  dependent-simple-category-tail (cons C' _ _ _)
    = C'

  dependent-simple-category-dependent-simple-functor (cons _ F _ _)
    = F

  dependent-simple-category-dependent-simple-functor-identity (cons _ _ p _)
    = p

  dependent-simple-category-dependent-simple-functor-compose (cons _ _ _ p)
    = p

  -- #### DependentSimpleFunctor
  
  data DependentSimpleFunctor where
  
    nil
      : {C D : ChainCategory zero}
      → {C' : DependentSimpleCategory C}
      → {D' : DependentSimpleCategory D}
      → {F : ChainFunctor C D}
      → Function
        (dependent-simple-category₀ C')
        (dependent-simple-category₀ D')
      → DependentSimpleFunctor C' D' F

    cons
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → {C' : DependentSimpleCategory C}
      → {D' : DependentSimpleCategory D}
      → {F : ChainFunctor C D}
      → (F' : (x : ChainCategory.Object C)
        → DependentSimpleFunctor
          (dependent-simple-category-tail C' x)
          (dependent-simple-category-tail D' (ChainFunctor.base F x))
          (ChainFunctor.tail F x))
      → ({x y : ChainCategory.Object C}
        → (f : ChainCategory.Arrow C x y)
        → DependentSimpleFunctorSquare
          (dependent-simple-category-dependent-simple-functor C' f)
          (dependent-simple-category-dependent-simple-functor D'
            (ChainFunctor.map F f))
          (F' x)
          (F' y))
      → DependentSimpleFunctor C' D' F

  dependent-simple-functor₀ (nil f)
    = f

  dependent-simple-functor-tail (cons F' _)
    = F'

  dependent-simple-functor-dependent-simple-functor-square (cons _ s)
    = s

  -- #### DependentSimpleFunctorIdentity
  
  data DependentSimpleFunctorIdentity where
  
    nil
      : {C : ChainCategory zero}
      → {C' : DependentSimpleCategory C}
      → {F : ChainFunctor C C}
      → {F' : DependentSimpleFunctor C' C' F}
      → FunctionIdentity
        (dependent-simple-functor₀ F')
      → DependentSimpleFunctorIdentity F'

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : DependentSimpleCategory C}
      → {F : ChainFunctor C C}
      → {F' : DependentSimpleFunctor C' C' F}
      → FunctorIdentity
        (ChainFunctor.head F)
      → ((x : ChainCategory.Object C)
        → DependentSimpleFunctorIdentity
          (dependent-simple-functor-tail F' x))
      → DependentSimpleFunctorIdentity F'

  dependent-simple-functor-identity₀ (nil p)
    = p

  dependent-simple-functor-identity-head (cons p _)
    = p

  dependent-simple-functor-identity-base p
    = FunctorIdentity.base
      (dependent-simple-functor-identity-head p)

  dependent-simple-functor-identity-tail (cons _ p)
    = p

  -- #### DependentSimpleFunctorCompose
  
  data DependentSimpleFunctorCompose where
  
    nil
      : {C D E : ChainCategory zero}
      → {C' : DependentSimpleCategory C}
      → {D' : DependentSimpleCategory D}
      → {E' : DependentSimpleCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : DependentSimpleFunctor D' E' F}
      → {G' : DependentSimpleFunctor C' D' G}
      → {H' : DependentSimpleFunctor C' E' H}
      → FunctionCompose
        (dependent-simple-functor₀ F')
        (dependent-simple-functor₀ G')
        (dependent-simple-functor₀ H')
      → DependentSimpleFunctorCompose F' G' H'

    cons
      : {n : ℕ}
      → {C D E : ChainCategory (suc n)}
      → {C' : DependentSimpleCategory C}
      → {D' : DependentSimpleCategory D}
      → {E' : DependentSimpleCategory E}
      → {F : ChainFunctor D E}
      → {G : ChainFunctor C D}
      → {H : ChainFunctor C E}
      → {F' : DependentSimpleFunctor D' E' F}
      → {G' : DependentSimpleFunctor C' D' G}
      → {H' : DependentSimpleFunctor C' E' H}
      → FunctorCompose
        (ChainFunctor.head F)
        (ChainFunctor.head G)
        (ChainFunctor.head H)
      → ((x : ChainCategory.Object C)
        → DependentSimpleFunctorCompose
          (dependent-simple-functor-tail F' (ChainFunctor.base G x))
          (dependent-simple-functor-tail G' x)
          (dependent-simple-functor-tail H' x))
      → DependentSimpleFunctorCompose F' G' H'

  dependent-simple-functor-compose₀ (nil p)
    = p

  dependent-simple-functor-compose-head (cons p _)
    = p

  dependent-simple-functor-compose-base p
    = FunctorCompose.base
      (dependent-simple-functor-compose-head p)

  dependent-simple-functor-compose-tail (cons _ p)
    = p

  -- #### DependentSimpleFunctorSquare
  
  data DependentSimpleFunctorSquare where
  
    nil
      : {C₁ C₂ D₁ D₂ : ChainCategory zero}
      → {C₁' : DependentSimpleCategory C₁}
      → {C₂' : DependentSimpleCategory C₂}
      → {D₁' : DependentSimpleCategory D₁}
      → {D₂' : DependentSimpleCategory D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : DependentSimpleFunctor C₁' C₂' F}
      → {G' : DependentSimpleFunctor D₁' D₂' G}
      → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
      → {H₂' : DependentSimpleFunctor C₂' D₂' H₂}
      → FunctionSquare
        (dependent-simple-functor₀ F')
        (dependent-simple-functor₀ G')
        (dependent-simple-functor₀ H₁')
        (dependent-simple-functor₀ H₂')
      → DependentSimpleFunctorSquare F' G' H₁' H₂'

    cons
      : {n : ℕ}
      → {C₁ C₂ D₁ D₂ : ChainCategory (suc n)}
      → {C₁' : DependentSimpleCategory C₁}
      → {C₂' : DependentSimpleCategory C₂}
      → {D₁' : DependentSimpleCategory D₁}
      → {D₂' : DependentSimpleCategory D₂}
      → {F : ChainFunctor C₁ C₂}
      → {G : ChainFunctor D₁ D₂}
      → {H₁ : ChainFunctor C₁ D₁}
      → {H₂ : ChainFunctor C₂ D₂}
      → {F' : DependentSimpleFunctor C₁' C₂' F}
      → {G' : DependentSimpleFunctor D₁' D₂' G}
      → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
      → {H₂' : DependentSimpleFunctor C₂' D₂' H₂}
      → FunctorSquare
        (ChainFunctor.head F)
        (ChainFunctor.head G)
        (ChainFunctor.head H₁)
        (ChainFunctor.head H₂)
      → ((x₁ : ChainCategory.Object C₁)
        → DependentSimpleFunctorSquare
          (dependent-simple-functor-tail F' x₁)
          (dependent-simple-functor-tail G' (ChainFunctor.base H₁ x₁))
          (dependent-simple-functor-tail H₁' x₁)
          (dependent-simple-functor-tail H₂' (ChainFunctor.base F x₁)))
      → DependentSimpleFunctorSquare F' G' H₁' H₂'

  dependent-simple-functor-square₀ (nil s)
    = s

  dependent-simple-functor-square-head (cons s _)
    = s

  dependent-simple-functor-square-base s
    = FunctorSquare.base
      (dependent-simple-functor-square-head s)

  dependent-simple-functor-square-tail (cons _ s)
    = s

-- ## Modules

-- ### DependentSimpleCategory

DependentSimpleCategory
  : {n : ℕ}
  → ChainCategory n
  → Set₁
DependentSimpleCategory
  = Internal.DependentSimpleCategory

open Internal.DependentSimpleCategory public

open Internal public
  using (dependent-simple-category₀)

module DependentSimpleCategory where

  open Internal public using () renaming
    ( dependent-simple-category-dependent-simple-functor
      to dependent-simple-functor
    ; dependent-simple-category-dependent-simple-functor-compose
      to dependent-simple-functor-compose
    ; dependent-simple-category-dependent-simple-functor-identity
      to dependent-simple-functor-identity
    ; dependent-simple-category-tail
      to tail
    )

-- ### DependentSimpleFunctor

DependentSimpleFunctor
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → DependentSimpleCategory C₁
  → DependentSimpleCategory C₂
  → ChainFunctor C₁ C₂
  → Set
DependentSimpleFunctor
  = Internal.DependentSimpleFunctor

open Internal.DependentSimpleFunctor public

open Internal public
  using (dependent-simple-functor₀)

module DependentSimpleFunctor where

  open Internal public using () renaming
    ( dependent-simple-functor-dependent-simple-functor-square
      to dependent-simple-functor-square
    ; dependent-simple-functor-tail
      to tail
    )

-- ### DependentSimpleFunctorIdentity

DependentSimpleFunctorIdentity
  : {n : ℕ}
  → {C₁ C₂ : ChainCategory n}
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {F : ChainFunctor C₁ C₂}
  → DependentSimpleFunctor C₁' C₂' F
  → Set
DependentSimpleFunctorIdentity
  = Internal.DependentSimpleFunctorIdentity

open Internal.DependentSimpleFunctorIdentity public

open Internal public
  using (dependent-simple-functor-identity₀)

module DependentSimpleFunctorIdentity where

  open Internal public using () renaming
    ( dependent-simple-functor-identity-base
      to base
    ; dependent-simple-functor-identity-head
      to head
    ; dependent-simple-functor-identity-tail
      to tail
    )

-- ### DependentSimpleFunctorCompose

DependentSimpleFunctorCompose
  : {n : ℕ}
  → {C D E₁ E₂ : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {E₁' : DependentSimpleCategory E₁}
  → {E₂' : DependentSimpleCategory E₂}
  → {F : ChainFunctor D E₁}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E₂}
  → DependentSimpleFunctor D' E₁' F
  → DependentSimpleFunctor C' D' G
  → DependentSimpleFunctor C' E₂' H
  → Set
DependentSimpleFunctorCompose
  = Internal.DependentSimpleFunctorCompose

open Internal.DependentSimpleFunctorCompose public

open Internal public
  using (dependent-simple-functor-compose₀)

module DependentSimpleFunctorCompose where

  open Internal public using () renaming
    ( dependent-simple-functor-compose-base
      to base
    ; dependent-simple-functor-compose-head
      to head
    ; dependent-simple-functor-compose-tail
      to tail
    )

-- ### DependentSimpleFunctorSquare

DependentSimpleFunctorSquare
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ D₃ : ChainCategory n}
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {D₁' : DependentSimpleCategory D₁}
  → {D₂' : DependentSimpleCategory D₂}
  → {D₃' : DependentSimpleCategory D₃}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₃}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → DependentSimpleFunctor C₁' C₂' F
  → DependentSimpleFunctor D₁' D₃' G
  → DependentSimpleFunctor C₁' D₁' H₁
  → DependentSimpleFunctor C₂' D₂' H₂
  → Set
DependentSimpleFunctorSquare
  = Internal.DependentSimpleFunctorSquare

open Internal.DependentSimpleFunctorSquare public

open Internal public
  using (dependent-simple-functor-square₀)

module DependentSimpleFunctorSquare where

  open Internal public using () renaming
    ( dependent-simple-functor-square-base
      to base
    ; dependent-simple-functor-square-head
      to head
    ; dependent-simple-functor-square-tail
      to tail
    )

