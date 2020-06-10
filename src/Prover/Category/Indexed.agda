module Prover.Category.Indexed where

open import Prover.Category
  using (Category; DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; Functor; FunctorCompose;
    FunctorIdentity; FunctorSquare)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory; ChainDependentFunctor;
    ChainFunctor)
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
    → (F' : IndexedFunctor C₁' C₂' F)
    → (G' : IndexedFunctor D₁' D₃' G)
    → (H₁' : IndexedFunctor C₁' D₁' H₁)
    → (H₂' : IndexedFunctor C₂' D₂' H₂)
    → Set
    
  -- #### IndexedDependentCategory
  
  record IndexedDependentCategory
    {n : ℕ}
    {C : Category}
    (C' : ChainDependentCategory C n)
    : Set₁
    
  -- #### IndexedDependentFunctor
  
  record IndexedDependentFunctor
    {n : ℕ}
    {C D : Category}
    {C' : ChainDependentCategory C n}
    {D' : ChainDependentCategory D n}
    (C'' : IndexedDependentCategory C')
    (D'' : IndexedDependentCategory D')
    (F : ChainDependentFunctor C' D')
    : Set
    
  -- #### IndexedDependentFunctorIdentity
  
  record IndexedDependentFunctorIdentity
    {n : ℕ}
    {C : Category}
    {C' : ChainDependentCategory C n}
    {C'' : IndexedDependentCategory C'}
    {F : ChainDependentFunctor C' C'}
    (F' : IndexedDependentFunctor C'' C'' F)
    : Set
    
  -- #### IndexedDependentFunctorCompose
  
  record IndexedDependentFunctorCompose
    {n : ℕ}
    {C D E : Category}
    {C' : ChainDependentCategory C n}
    {D' : ChainDependentCategory D n}
    {E' : ChainDependentCategory E n}
    {C'' : IndexedDependentCategory C'}
    {D'' : IndexedDependentCategory D'}
    {E'' : IndexedDependentCategory E'}
    {F : ChainDependentFunctor D' E'}
    {G : ChainDependentFunctor C' D'}
    {H : ChainDependentFunctor C' E'}
    (F' : IndexedDependentFunctor D'' E'' F)
    (G' : IndexedDependentFunctor C'' D'' G)
    (H' : IndexedDependentFunctor C'' E'' H)
    : Set
  
  -- #### IndexedDependentFunctorSquare
  
  record IndexedDependentFunctorSquare
    {n : ℕ}
    {C₁ C₂ D₁ D₂ : Category}
    {C₁' : ChainDependentCategory C₁ n}
    {C₂' : ChainDependentCategory C₂ n}
    {D₁' : ChainDependentCategory D₁ n}
    {D₂' : ChainDependentCategory D₂ n}
    {C₁'' : IndexedDependentCategory C₁'}
    {C₂'' : IndexedDependentCategory C₂'}
    {D₁'' : IndexedDependentCategory D₁'}
    {D₂'' : IndexedDependentCategory D₂'}
    {F : ChainDependentFunctor C₁' C₂'}
    {G : ChainDependentFunctor D₁' D₂'}
    {H₁ : ChainDependentFunctor C₁' D₁'}
    {H₂ : ChainDependentFunctor C₂' D₂'}
    (F' : IndexedDependentFunctor C₁'' C₂'' F)
    (G' : IndexedDependentFunctor D₁'' D₂'' G)
    (H₁' : IndexedDependentFunctor C₁'' D₁'' H₁)
    (H₂' : IndexedDependentFunctor C₂'' D₂'' H₂)
    : Set
    
  -- ### Interface
  
  -- #### IndexedCategory
  
  indexed-category₀
    : {C : ChainCategory zero}
    → IndexedCategory C
    → Category
  
  indexed-category-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedCategory C
    → IndexedDependentCategory
      (ChainCategory.unpack C)

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
  
  indexed-functor-unpack
    : {n : ℕ}
    → {C D : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → {D' : IndexedCategory D}
    → {F : ChainFunctor C D}
    → IndexedFunctor C' D' F
    → IndexedDependentFunctor
      (indexed-category-unpack C')
      (indexed-category-unpack D')
      (ChainFunctor.unpack F)
  
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

  indexed-functor-identity-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → {F : ChainFunctor C C}
    → {F' : IndexedFunctor C' C' F}
    → IndexedFunctorIdentity F'
    → IndexedDependentFunctorIdentity
      (indexed-functor-unpack F')

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

  indexed-functor-compose-unpack
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
    → IndexedDependentFunctorCompose
      (indexed-functor-unpack F')
      (indexed-functor-unpack G')
      (indexed-functor-unpack H')

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

  indexed-functor-square-unpack
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
    → IndexedDependentFunctorSquare
      (indexed-functor-unpack F')
      (indexed-functor-unpack G')
      (indexed-functor-unpack H₁')
      (indexed-functor-unpack H₂')

  -- ### Definitions
  
  -- #### IndexedCategory
  
  data IndexedCategory where
  
    empty
      : {C : ChainCategory zero}
      → Category
      → IndexedCategory C

    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → IndexedDependentCategory
        (ChainCategory.unpack C)
      → IndexedCategory C
  
  indexed-category₀ (empty C)
    = C

  indexed-category-unpack (sigma C)
    = C
  
  -- #### IndexedFunctor
  
  data IndexedFunctor where
  
    empty
      : {C D : ChainCategory zero}
      → {C' : IndexedCategory C}
      → {D' : IndexedCategory D}
      → {F : ChainFunctor C D}
      → Functor
        (indexed-category₀ C')
        (indexed-category₀ D')
      → IndexedFunctor C' D' F
  
    sigma
      : {n : ℕ}
      → {C D : ChainCategory (suc n)}
      → {C' : IndexedCategory C}
      → {D' : IndexedCategory D}
      → {F : ChainFunctor C D}
      → IndexedDependentFunctor
        (indexed-category-unpack C')
        (indexed-category-unpack D')
        (ChainFunctor.unpack F)
      → IndexedFunctor C' D' F
  
  indexed-functor₀ (empty F)
    = F
  
  indexed-functor-unpack (sigma F)
    = F
  
  -- #### IndexedFunctorIdentity
  
  data IndexedFunctorIdentity where
  
    empty
      : {C : ChainCategory zero}
      → {C' : IndexedCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedFunctor C' C' F}
      → FunctorIdentity
        (indexed-functor₀ F')
      → IndexedFunctorIdentity F'

    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : IndexedCategory C}
      → {F : ChainFunctor C C}
      → {F' : IndexedFunctor C' C' F}
      → IndexedDependentFunctorIdentity
        (indexed-functor-unpack F')
      → IndexedFunctorIdentity F'
  
  indexed-functor-identity₀ (empty p)
    = p

  indexed-functor-identity₀-eq _ _ refl
    = indexed-functor-identity₀

  indexed-functor-identity-unpack (sigma p)
    = p

  -- #### IndexedFunctorCompose
  
  data IndexedFunctorCompose where
  
    empty
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
  
    sigma
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
      → IndexedDependentFunctorCompose
        (indexed-functor-unpack F')
        (indexed-functor-unpack G')
        (indexed-functor-unpack H')
      → IndexedFunctorCompose F' G' H'
  
  indexed-functor-compose₀ (empty p)
    = p

  indexed-functor-compose₀-eq _ _ refl
    = indexed-functor-compose₀

  indexed-functor-compose-unpack (sigma p)
    = p

  -- #### IndexedFunctorSquare
  
  data IndexedFunctorSquare where
  
    empty
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
  
    sigma
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
      → IndexedDependentFunctorSquare
        (indexed-functor-unpack F')
        (indexed-functor-unpack G')
        (indexed-functor-unpack H₁')
        (indexed-functor-unpack H₂')
      → IndexedFunctorSquare F' G' H₁' H₂'
  
  indexed-functor-square₀ (empty s)
    = s

  indexed-functor-square₀-eq _ _ refl
    = indexed-functor-square₀

  indexed-functor-square-unpack (sigma s)
    = s

  -- #### IndexedDependentCategory
  
  record IndexedDependentCategory
    {_ C} C'
    where

    inductive

    no-eta-equality

    constructor
      
      indexed-dependent-category

    field

      indexed-category
        : (x : Category.Object C)
        → IndexedCategory
          (ChainDependentCategory.chain-category C' x)

      indexed-functor
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → IndexedFunctor
          (indexed-category x)
          (indexed-category y)
          (ChainDependentCategory.chain-functor C' f)

      indexed-functor-identity
        : (x : Category.Object C)
        → IndexedFunctorIdentity
          (indexed-functor (Category.identity C x))
  
      indexed-functor-compose
        : {x y z : Category.Object C}
        → (f : Category.Arrow C y z)
        → (g : Category.Arrow C x y)
        → IndexedFunctorCompose
          (indexed-functor f)
          (indexed-functor g)
          (indexed-functor (Category.compose C f g))
  
  -- #### IndexedDependentFunctor
  
  record IndexedDependentFunctor
    {_ C} C'' D'' F
    where

    inductive

    no-eta-equality

    constructor

      indexed-dependent-functor

    field

      indexed-functor
        : (x : Category.Object C)
        → IndexedFunctor
          (IndexedDependentCategory.indexed-category C'' x)
          (IndexedDependentCategory.indexed-category D''
            (ChainDependentFunctor.base F x))
          (ChainDependentFunctor.chain-functor F x)

      indexed-functor-square
        : {x y : Category.Object C}
        → (f : Category.Arrow C x y)
        → IndexedFunctorSquare
          (IndexedDependentCategory.indexed-functor C'' f)
          (IndexedDependentCategory.indexed-functor D''
            (ChainDependentFunctor.map F f))
          (indexed-functor x)
          (indexed-functor y)
  
  -- #### IndexedDependentFunctorIdentity
  
  record IndexedDependentFunctorIdentity
    {_ C _ _ F} F'
    where

    inductive

    constructor

      indexed-dependent-functor-identity

    field

      functor
        : FunctorIdentity
          (ChainDependentFunctor.functor F)
  
    open FunctorIdentity functor public
  
    field
  
      indexed-functor
        : (x : Category.Object C)
        → IndexedFunctorIdentity
          (IndexedDependentFunctor.indexed-functor F' x)
  
  -- #### IndexedDependentFunctorCompose
  
  record IndexedDependentFunctorCompose
    {_ C _ _ _ _ _ _ _ _ F G H} F' G' H'
    where

    inductive

    constructor

      indexed-dependent-functor-compose

    field

      functor
        : FunctorCompose
          (ChainDependentFunctor.functor F)
          (ChainDependentFunctor.functor G)
          (ChainDependentFunctor.functor H)
  
    open FunctorCompose functor public
  
    field
  
      indexed-functor
        : (x : Category.Object C)
        → IndexedFunctorCompose
          (IndexedDependentFunctor.indexed-functor F'
            (ChainDependentFunctor.base G x))
          (IndexedDependentFunctor.indexed-functor G' x)
          (IndexedDependentFunctor.indexed-functor H' x)
  
  -- #### IndexedDependentFunctorSquare

  record IndexedDependentFunctorSquare
    {_ C₁ _ _ _ _ _ _ _ _ _ _ _ F G H₁ H₂} F' G' H₁' H₂'
    where

    inductive

    constructor

      indexed-dependent-functor-square

    field

      functor
        : FunctorSquare
          (ChainDependentFunctor.functor F)
          (ChainDependentFunctor.functor G)
          (ChainDependentFunctor.functor H₁)
          (ChainDependentFunctor.functor H₂)
  
    open FunctorSquare functor public
  
    field
  
      indexed-functor
        : (x₁ : Category.Object C₁)
        → IndexedFunctorSquare
          (IndexedDependentFunctor.indexed-functor F' x₁)
          (IndexedDependentFunctor.indexed-functor G'
            (ChainDependentFunctor.base H₁ x₁))
          (IndexedDependentFunctor.indexed-functor H₁' x₁)
          (IndexedDependentFunctor.indexed-functor H₂'
            (ChainDependentFunctor.base F x₁))

  -- ### Destruction

  -- #### IndexedDependentCategory

  module _
    {C : Category}
    {C' : ChainDependentCategory C zero}
    where
  
    module IndexedDependentCategory₀
      (C'' : IndexedDependentCategory C')
      where
    
      category
        : Category.Object C
        → Category
      category x
        = indexed-category₀
          (IndexedDependentCategory.indexed-category C'' x)
  
      functor
        : {x y : Category.Object C}
        → Category.Arrow C x y
        → Functor
          (category x)
          (category y)
      functor f
        = indexed-functor₀
          (IndexedDependentCategory.indexed-functor C'' f)
  
      abstract

        functor-identity
          : (x : Category.Object C)
          → FunctorIdentity
            (functor (Category.identity C x))
        functor-identity x
          = indexed-functor-identity₀
            (IndexedDependentCategory.indexed-functor-identity C'' x)
    
        functor-compose
          : {x y z : Category.Object C}
          → (f : Category.Arrow C y z)
          → (g : Category.Arrow C x y)
          → FunctorCompose
            (functor f)
            (functor g)
            (functor (Category.compose C f g))
        functor-compose f g
          = indexed-functor-compose₀
            (IndexedDependentCategory.indexed-functor-compose C'' f g)
  
    indexed-dependent-category₀
      : IndexedDependentCategory C'
      → DependentCategory C
    indexed-dependent-category₀ C''
      = record {IndexedDependentCategory₀ C''}
  
  -- #### IndexedDependentFunctor
  
  module _
    {C D : Category}
    {C' : ChainDependentCategory C zero}
    {D' : ChainDependentCategory D zero}
    {C'' : IndexedDependentCategory C'}
    {D'' : IndexedDependentCategory D'}
    {F : ChainDependentFunctor C' D'}
    where
  
    module IndexedDependentFunctor₀
      (F' : IndexedDependentFunctor C'' D'' F)
      where
  
      functor
        : Functor C D
      functor
        = ChainDependentFunctor.functor F
  
      open Functor functor
  
      functor'
        : (x : Category.Object C)
        → Functor
          (DependentCategory.category
            (indexed-dependent-category₀ C'') x)
          (DependentCategory.category
            (indexed-dependent-category₀ D'') (base x))
      functor' x
        = indexed-functor₀
          (IndexedDependentFunctor.indexed-functor F' x)
  
      abstract

        functor-square
          : {x y : Category.Object C}
          → (f : Category.Arrow C x y)
          → FunctorSquare
            (DependentCategory.functor
              (indexed-dependent-category₀ C'') f)
            (DependentCategory.functor
              (indexed-dependent-category₀ D'') (map f))
            (functor' x)
            (functor' y)
        functor-square f
          = indexed-functor-square₀
            (IndexedDependentFunctor.indexed-functor-square F' f)
  
    indexed-dependent-functor₀
      : IndexedDependentFunctor C'' D'' F
      → DependentFunctor
        (indexed-dependent-category₀ C'')
        (indexed-dependent-category₀ D'')
    indexed-dependent-functor₀ F'
      = record {IndexedDependentFunctor₀ F'}
  
  -- #### IndexedDependentFunctorIdentity
  
  module _
    {C : Category}
    {C' : ChainDependentCategory C zero}
    {C'' : IndexedDependentCategory C'}
    {F : ChainDependentFunctor C' C'}
    {F' : IndexedDependentFunctor C'' C'' F}
    where

    module IndexedDependentFunctorIdentity₀
      (p : IndexedDependentFunctorIdentity F')
      where

      functor
        : FunctorIdentity
          (DependentFunctor.functor (indexed-dependent-functor₀ F'))
      functor
        = IndexedDependentFunctorIdentity.functor p
          
      functor'
        : (x : Category.Object C)
        → FunctorIdentity
          (DependentFunctor.functor' (indexed-dependent-functor₀ F') x)
      functor' x
        = indexed-functor-identity₀-eq
          (ChainDependentCategory.chain-category C')
          (IndexedDependentCategory.indexed-category C'')
          (IndexedDependentFunctorIdentity.base p x)
          (IndexedDependentFunctorIdentity.indexed-functor p x)

    indexed-dependent-functor-identity₀
      : IndexedDependentFunctorIdentity F'
      → DependentFunctorIdentity
        (indexed-dependent-functor₀ F')
    indexed-dependent-functor-identity₀ p
      = record {IndexedDependentFunctorIdentity₀ p}

  -- #### IndexedDependentFunctorCompose
  
  module _
    {C D E : Category}
    {C' : ChainDependentCategory C zero}
    {D' : ChainDependentCategory D zero}
    {E' : ChainDependentCategory E zero}
    {C'' : IndexedDependentCategory C'}
    {D'' : IndexedDependentCategory D'}
    {E'' : IndexedDependentCategory E'}
    {F : ChainDependentFunctor D' E'}
    {G : ChainDependentFunctor C' D'}
    {H : ChainDependentFunctor C' E'}
    {F' : IndexedDependentFunctor D'' E'' F}
    {G' : IndexedDependentFunctor C'' D'' G}
    {H' : IndexedDependentFunctor C'' E'' H}
    where

    module IndexedDependentFunctorCompose₀
      (p : IndexedDependentFunctorCompose F' G' H')
      where

      functor
        : FunctorCompose
          (DependentFunctor.functor (indexed-dependent-functor₀ F'))
          (DependentFunctor.functor (indexed-dependent-functor₀ G'))
          (DependentFunctor.functor (indexed-dependent-functor₀ H'))
      functor
        = IndexedDependentFunctorCompose.functor p
  
      functor'
        : (x : Category.Object C)
        → FunctorCompose
          (DependentFunctor.functor' (indexed-dependent-functor₀ F')
            (DependentFunctor.base (indexed-dependent-functor₀ G') x))
          (DependentFunctor.functor' (indexed-dependent-functor₀ G') x)
          (DependentFunctor.functor' (indexed-dependent-functor₀ H') x)
      functor' x
        = indexed-functor-compose₀-eq
          (ChainDependentCategory.chain-category E')
          (IndexedDependentCategory.indexed-category E'')
          (IndexedDependentFunctorCompose.base p x)
          (IndexedDependentFunctorCompose.indexed-functor p x)

    indexed-dependent-functor-compose₀
      : IndexedDependentFunctorCompose F' G' H'
      → DependentFunctorCompose
        (indexed-dependent-functor₀ F')
        (indexed-dependent-functor₀ G')
        (indexed-dependent-functor₀ H')
    indexed-dependent-functor-compose₀ p
      = record {IndexedDependentFunctorCompose₀ p}

  -- #### IndexedDependentFunctorSquare
  
  module _
    {C₁ C₂ D₁ D₂ : Category}
    {C₁' : ChainDependentCategory C₁ zero}
    {C₂' : ChainDependentCategory C₂ zero}
    {D₁' : ChainDependentCategory D₁ zero}
    {D₂' : ChainDependentCategory D₂ zero}
    {C₁'' : IndexedDependentCategory C₁'}
    {C₂'' : IndexedDependentCategory C₂'}
    {D₁'' : IndexedDependentCategory D₁'}
    {D₂'' : IndexedDependentCategory D₂'}
    {F : ChainDependentFunctor C₁' C₂'}
    {G : ChainDependentFunctor D₁' D₂'}
    {H₁ : ChainDependentFunctor C₁' D₁'}
    {H₂ : ChainDependentFunctor C₂' D₂'}
    {F' : IndexedDependentFunctor C₁'' C₂'' F}
    {G' : IndexedDependentFunctor D₁'' D₂'' G}
    {H₁' : IndexedDependentFunctor C₁'' D₁'' H₁}
    {H₂' : IndexedDependentFunctor C₂'' D₂'' H₂}
    where

    module IndexedDependentFunctorSquare₀
      (s : IndexedDependentFunctorSquare F' G' H₁' H₂')
      where

      functor
        : FunctorSquare
          (DependentFunctor.functor (indexed-dependent-functor₀ F'))
          (DependentFunctor.functor (indexed-dependent-functor₀ G'))
          (DependentFunctor.functor (indexed-dependent-functor₀ H₁'))
          (DependentFunctor.functor (indexed-dependent-functor₀ H₂'))
      functor
        = IndexedDependentFunctorSquare.functor s
  
      functor'
        : (x₁ : Category.Object C₁)
        → FunctorSquare
          (DependentFunctor.functor' (indexed-dependent-functor₀ F') x₁)
          (DependentFunctor.functor' (indexed-dependent-functor₀ G')
            (DependentFunctor.base (indexed-dependent-functor₀ H₁') x₁))
          (DependentFunctor.functor' (indexed-dependent-functor₀ H₁') x₁)
          (DependentFunctor.functor' (indexed-dependent-functor₀ H₂')
            (DependentFunctor.base (indexed-dependent-functor₀ F') x₁))
      functor' x₁
        = indexed-functor-square₀-eq
          (ChainDependentCategory.chain-category D₂')
          (IndexedDependentCategory.indexed-category D₂'')
          (IndexedDependentFunctorSquare.base s x₁)
          (IndexedDependentFunctorSquare.indexed-functor s x₁)

    indexed-dependent-functor-square₀
      : IndexedDependentFunctorSquare F' G' H₁' H₂'
      → DependentFunctorSquare
        (indexed-dependent-functor₀ F')
        (indexed-dependent-functor₀ G')
        (indexed-dependent-functor₀ H₁')
        (indexed-dependent-functor₀ H₂')
    indexed-dependent-functor-square₀ s
      = record {IndexedDependentFunctorSquare₀ s}

  -- ### Tail

  indexed-category-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedCategory C
    → (x : Category.Object (ChainCategory.head C))
    → IndexedCategory (ChainCategory.tail C x)
  indexed-category-tail C' x
    = IndexedDependentCategory.indexed-category
      (indexed-category-unpack C') x

-- ## Modules

open Internal public
  using (IndexedDependentCategory; IndexedDependentFunctor;
    IndexedDependentFunctorCompose; IndexedDependentFunctorIdentity;
    IndexedDependentFunctorSquare; indexed-dependent-category;
    indexed-dependent-category₀; indexed-dependent-functor;
    indexed-dependent-functor₀; indexed-dependent-functor-compose;
    indexed-dependent-functor-compose₀; indexed-dependent-functor-identity;
    indexed-dependent-functor-identity₀; indexed-dependent-functor-square;
    indexed-dependent-functor-square₀)

-- ### IndexedCategory

IndexedCategory
  : {n : ℕ}
  → ChainCategory n
  → Set₁
IndexedCategory
  = Internal.IndexedCategory
  
open Internal.IndexedCategory public

open Internal public
  using (indexed-category₀)

module IndexedCategory where

  open Internal.IndexedCategory public

  open Internal public using () renaming
    ( indexed-category-tail
      to tail
    ; indexed-category-unpack
      to unpack
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
  using (indexed-functor₀)

module IndexedFunctor where

  open Internal.IndexedFunctor public

  open Internal public using () renaming
    ( indexed-functor-unpack
      to unpack
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
  using (indexed-functor-identity₀; indexed-functor-identity₀-eq)

module IndexedFunctorIdentity where

  open Internal.IndexedFunctorIdentity public

  open Internal public using () renaming
    ( indexed-functor-identity-unpack
      to unpack
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
  using (indexed-functor-compose₀; indexed-functor-compose₀-eq)

module IndexedFunctorCompose where

  open Internal.IndexedFunctorCompose public

  open Internal public using () renaming
    ( indexed-functor-compose-unpack
      to unpack
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
  → (F' : IndexedFunctor C₁' C₂' F)
  → (G' : IndexedFunctor D₁' D₃' G)
  → (H₁' : IndexedFunctor C₁' D₁' H₁)
  → (H₂' : IndexedFunctor C₂' D₂' H₂)
  → Set
IndexedFunctorSquare
  = Internal.IndexedFunctorSquare
  
open Internal.IndexedFunctorSquare public

open Internal public
  using (indexed-functor-square₀; indexed-functor-square₀-eq)

module IndexedFunctorSquare where

  open Internal.IndexedFunctorSquare public

  open Internal public using () renaming
    ( indexed-functor-square-unpack
      to unpack
    )

