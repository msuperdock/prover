module Prover.Category.Partial.List where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.List
  using (module CategoryList; module FunctorList; category-list; functor-list)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Prelude

open List
  using (_!_)

-- ## PartialFunctor

module _
  {C D : Category}
  where

  module PartialFunctorList
    (F : PartialFunctor C D)
    where

    base
      : Category.Object (category-list C)
      → Maybe (Category.Object (category-list D))
    base
      = List.map-maybe
        (PartialFunctor.base F)

    map-lookup
      : {xs ys : Category.Object (category-list C)}
      → {xs' ys' : Category.Object (category-list D)}
      → base xs ≡ just xs'
      → base ys ≡ just ys'
      → Category.Arrow (category-list C) xs ys
      → (k : Fin (List.length xs'))
      → Maybe (l ∈ Fin (List.length ys')
        × Category.Arrow D (xs' ! k) (ys' ! l))
    map-lookup {xs = any xs} {ys = any ys} _ _ fs k
      with Vec.map-maybe (PartialFunctor.base F) xs
      | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
      | Vec.map-maybe (PartialFunctor.base F) ys
      | inspect (Vec.map-maybe (PartialFunctor.base F)) ys
    map-lookup {xs = any xs} {ys = any ys} refl refl fs k
      | just _ | [ p ] | just _ | [ q ]
      with CategoryList.Arrow.lookup fs k
    ... | nothing
      = nothing
    ... | just (l , f)
      = just (l , PartialFunctor.map F
        (Vec.lookup-map-maybe (PartialFunctor.base F) xs p k)
        (Vec.lookup-map-maybe (PartialFunctor.base F) ys q l) f)

    abstract

      map-injective
        : {xs ys : Category.Object (category-list C)}
        → {xs' ys' : Category.Object (category-list D)}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → (f : Category.Arrow (category-list C) xs ys)
        → (k₁ k₂ : Fin (List.length xs'))
        → {l : Fin (List.length ys')}
        → {g₁ : Category.Arrow D (xs' ! k₁) (ys' ! l)}
        → {g₂ : Category.Arrow D (xs' ! k₂) (ys' ! l)}
        → map-lookup p q f k₁ ≡ just (l , g₁)
        → map-lookup p q f k₂ ≡ just (l , g₂)
        → k₁ ≡ k₂
      map-injective {xs = any xs} {ys = any ys} _ _ _ _ _ _ _
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
        | Vec.map-maybe (PartialFunctor.base F) ys
        | inspect (Vec.map-maybe (PartialFunctor.base F)) ys
      map-injective refl refl f k₁ k₂ _ _
        | just _ | [ _ ] | just _ | [ _ ]
        with CategoryList.Arrow.lookup f k₁
        | inspect (CategoryList.Arrow.lookup f) k₁
        | CategoryList.Arrow.lookup f k₂
        | inspect (CategoryList.Arrow.lookup f) k₂
      map-injective _ _ f k₁ k₂ refl refl
        | _ | _ | _ | _ | just _ | [ p₁ ] | just _ | [ p₂ ]
        = CategoryList.Arrow.injective f k₁ k₂ p₁ p₂

    map
      : {xs ys : Category.Object (category-list C)}
      → {xs' ys' : Category.Object (category-list D)}
      → base xs ≡ just xs'
      → base ys ≡ just ys'
      → Category.Arrow (category-list C) xs ys
      → Category.Arrow (category-list D) xs' ys'
    map p q fs
      = record
      { lookup
        = map-lookup p q fs
      ; injective
        = map-injective p q fs
      }

    abstract

      map-equal'
        : {xs ys : Category.Object (category-list C)}
        → {xs' ys' : Category.Object (category-list D)}
        → {fs₁ fs₂ : Category.Arrow (category-list C) xs ys}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → Category.ArrowEqual (category-list C) fs₁ fs₂
        → (k : Fin (List.length xs'))
        → CategoryList.LookupEqual D xs' ys' k
          (map-lookup p q fs₁ k)
          (map-lookup p q fs₂ k)
      map-equal' {xs = any xs} {ys = any ys} _ _ _ _
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
        | Vec.map-maybe (PartialFunctor.base F) ys
        | inspect (Vec.map-maybe (PartialFunctor.base F)) ys
      map-equal' {xs = any xs} {ys = any ys} {fs₁ = fs₁} {fs₂ = fs₂}
        refl refl rs k
        | just _ | [ p ] | just _ | [ q ]
        with CategoryList.Arrow.lookup fs₁ k
        | CategoryList.Arrow.lookup fs₂ k
        | CategoryList.ArrowEqual.lookup rs k
      ... | _ | _ | CategoryList.nothing
        = CategoryList.nothing
      ... | _ | _ | CategoryList.just l r
        = CategoryList.just l
        $ PartialFunctor.map-equal F
          (Vec.lookup-map-maybe (PartialFunctor.base F) xs p k)
          (Vec.lookup-map-maybe (PartialFunctor.base F) ys q l) r

      map-equal
        : {xs ys : Category.Object (category-list C)}
        → {xs' ys' : Category.Object (category-list D)}
        → {fs₁ fs₂ : Category.Arrow (category-list C) xs ys}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → Category.ArrowEqual (category-list C) fs₁ fs₂
        → Category.ArrowEqual (category-list D) (map p q fs₁) (map p q fs₂)
      map-equal p q rs
        = record
        { lookup
          = map-equal' p q rs
        }

      map-identity'
        : {xs' : Category.Object (category-list D)}
        → (xs : Category.Object (category-list C))
        → (p : base xs ≡ just xs')
        → (k : Fin (List.length xs'))
        → CategoryList.LookupEqual D xs' xs' k
          (map-lookup p p (Category.identity (category-list C) xs) k)
          (CategoryList.identity-lookup D xs' k)
      map-identity' (any xs) _ _
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
      map-identity' (any xs) refl k
        | just _ | [ p ]
        = CategoryList.just k
        $ PartialFunctor.map-identity F
          (Vec.lookup xs k)
          (Vec.lookup-map-maybe (PartialFunctor.base F) xs p k)

      map-identity
        : {xs' : Category.Object (category-list D)}
        → (xs : Category.Object (category-list C))
        → (p : base xs ≡ just xs')
        → Category.ArrowEqual (category-list D)
          (map p p (Category.identity (category-list C) xs))
          (Category.identity (category-list D) xs')
      map-identity xs p
        = record
        { lookup
          = map-identity' xs p
        }

      map-compose'
        : {xs ys zs : Category.Object (category-list C)}
        → {xs' ys' zs' : Category.Object (category-list D)}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → (r : base zs ≡ just zs')
        → (fs : Category.Arrow (category-list C) ys zs)
        → (gs : Category.Arrow (category-list C) xs ys)
        → (k : Fin (List.length xs'))
        → CategoryList.LookupEqual D xs' zs' k
          (map-lookup p r (Category.compose (category-list C) fs gs) k)
          (CategoryList.compose-lookup D (map q r fs) (map p q gs) k)
      map-compose' p q _ _ gs k
        with map-lookup p q gs k
        | inspect (map-lookup p q gs) k

      map-compose' {xs = any xs} {ys = any ys} {zs = any zs} _ _ _ _ _ _
        | nothing | [ _ ]
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
        | Vec.map-maybe (PartialFunctor.base F) ys
        | inspect (Vec.map-maybe (PartialFunctor.base F)) ys
        | Vec.map-maybe (PartialFunctor.base F) zs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) zs
      map-compose' refl refl refl _ gs k
        | _ | _ | just _ | _ | just _ | _ | just _ | _
        with CategoryList.Arrow.lookup gs k
      ... | nothing
        = CategoryList.nothing

      map-compose' _ q r fs _ _
        | just (l , _) | [ _ ]
        with map-lookup q r fs l
        | inspect (map-lookup q r fs) l

      map-compose' {xs = any xs} {ys = any ys} {zs = any zs} _ _ _ _ _ _
        | _ | _ | nothing | [ _ ]
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
        | Vec.map-maybe (PartialFunctor.base F) ys
        | inspect (Vec.map-maybe (PartialFunctor.base F)) ys
        | Vec.map-maybe (PartialFunctor.base F) zs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) zs
      map-compose' refl refl refl _ gs k
        | _ | _ | _ | _ | just _ | _ | just _ | _ | just _ | _
        with CategoryList.Arrow.lookup gs k
      map-compose' _ _ _ fs _ _
        | _ | [ refl ] | _ | _ | _ | _ | _ | _ | _ | _ | just (l , _)
        with CategoryList.Arrow.lookup fs l
      ... | nothing
        = CategoryList.nothing

      map-compose' {xs = any xs} {ys = any ys} {zs = any zs} _ _ _ _ _ _
        | _ | _ | just _ | [ _ ]
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
        | Vec.map-maybe (PartialFunctor.base F) ys
        | inspect (Vec.map-maybe (PartialFunctor.base F)) ys
        | Vec.map-maybe (PartialFunctor.base F) zs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) zs
      map-compose' refl refl refl _ gs k
        | _ | _ | _ | _ | just _ | _ | just _ | _ | just _ | _
        with CategoryList.Arrow.lookup gs k
      map-compose' _ _ _ fs _ _
        | _ | [ refl ] | _ | _ | _ | _ | _ | _ | _ | _ | just (l , _)
        with CategoryList.Arrow.lookup fs l
      map-compose' {xs = any xs} {ys = any ys} {zs = any zs} _ _ _ _ _ k
        | _ | _ | _ | [ refl ] | _ | [ p ] | _ | [ q ] | _ | [ r ]
        | just (l , g) | just (m , f)
        = CategoryList.just m
        $ PartialFunctor.map-compose F
          (Vec.lookup-map-maybe (PartialFunctor.base F) xs p k)
          (Vec.lookup-map-maybe (PartialFunctor.base F) ys q l)
          (Vec.lookup-map-maybe (PartialFunctor.base F) zs r m) f g

      map-compose
        : {xs ys zs : Category.Object (category-list C)}
        → {xs' ys' zs' : Category.Object (category-list D)}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → (r : base zs ≡ just zs')
        → (fs : Category.Arrow (category-list C) ys zs)
        → (gs : Category.Arrow (category-list C) xs ys)
        → Category.ArrowEqual (category-list D)
          (map p r (Category.compose (category-list C) fs gs))
          (Category.compose (category-list D) (map q r fs) (map p q gs))
      map-compose p q r fs gs
        = record
        { lookup
          = map-compose' p q r fs gs
        }

  partial-functor-list
    : PartialFunctor C D
    → PartialFunctor
      (category-list C)
      (category-list D)
  partial-functor-list F
    = record {PartialFunctorList F}

-- ## PartialFunctorSquare

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : PartialFunctor C₁ D₁}
  {H₂ : PartialFunctor C₂ D₂}
  where

  module PartialFunctorSquareList
    (s : PartialFunctorSquare F G H₁ H₂)
    where

    base'
      : {n : ℕ}
      → {xs₁' : Vec (Category.Object D₁) n}
      → (xs₁ : Vec (Category.Object C₁) n)
      → Vec.map-maybe (PartialFunctor.base H₁) xs₁ ≡ just xs₁'
      → (k : Fin n)
      → PartialFunctor.base H₂ (Vec.lookup (Vec.map (Functor.base F) xs₁) k)
        ≡ just (Vec.lookup (Vec.map (Functor.base G) xs₁') k)
    base' {xs₁' = xs₁'} xs₁ p₁ k
      with Vec.lookup (Vec.map (Functor.base F) xs₁) k
      | Vec.lookup-map (Functor.base F) xs₁ k
      | Vec.lookup (Vec.map (Functor.base G) xs₁') k
      | Vec.lookup-map (Functor.base G) xs₁' k
    ... | _ | refl | _ | refl
      = PartialFunctorSquare.base s (Vec.lookup xs₁ k)
      $ Vec.lookup-map-maybe (PartialFunctor.base H₁) xs₁ p₁ k

    base
      : {xs₁' : Category.Object (category-list D₁)}
      → (xs₁ : Category.Object (category-list C₁))
      → PartialFunctor.base (partial-functor-list H₁) xs₁ ≡ just xs₁'
      → PartialFunctor.base (partial-functor-list H₂)
        (Functor.base (functor-list F) xs₁)
      ≡ just (Functor.base (functor-list G) xs₁')
    base (any xs₁) _
      with Vec.map-maybe (PartialFunctor.base H₁) xs₁
      | inspect (Vec.map-maybe (PartialFunctor.base H₁)) xs₁
    base {xs₁' = any xs₁'} (any xs₁) refl | just _ | [ p₁ ]
      with Vec.map-maybe 
        (PartialFunctor.base H₂)
        (Vec.map (Functor.base F) xs₁)
      | Vec.lookup-map-maybe'
        (PartialFunctor.base H₂)
        (Vec.map (Functor.base F) xs₁)
        (Vec.map (Functor.base G) xs₁')
        (base' xs₁ p₁)
    ... | _ | refl
      = refl

    map'
      : {xs₁ ys₁ : Category.Object (category-list C₁)}
      → {xs₁' ys₁' : Category.Object (category-list D₁)}
      → (p₁ : PartialFunctor.base (partial-functor-list H₁) xs₁ ≡ just xs₁')
      → (q₁ : PartialFunctor.base (partial-functor-list H₁) ys₁ ≡ just ys₁')
      → (fs₁ : Category.Arrow (category-list C₁) xs₁ ys₁)
      → (k : Fin (List.length xs₁'))
      → CategoryList.LookupEqual D₂
        (Functor.base (functor-list G) xs₁')
        (Functor.base (functor-list G) ys₁') k
        (PartialFunctorList.map-lookup H₂ (base xs₁ p₁) (base ys₁ q₁)
          (Functor.map (functor-list F) fs₁) k)
        (FunctorList.map-lookup G
          (PartialFunctor.map (partial-functor-list H₁) p₁ q₁ fs₁) k)
    map' {xs₁ = any xs₁} {ys₁ = any ys₁} p₁ q₁ fs₁ _
      with PartialFunctor.map (partial-functor-list H₁) p₁ q₁ fs₁
      | inspect CategoryList.Arrow.lookup
        (PartialFunctor.map (partial-functor-list H₁) p₁ q₁ fs₁)
    ... | _ | _
      with Vec.map-maybe (PartialFunctor.base H₁) xs₁
      | inspect (Vec.map-maybe (PartialFunctor.base H₁)) xs₁
      | Vec.map-maybe (PartialFunctor.base H₁) ys₁
      | inspect (Vec.map-maybe (PartialFunctor.base H₁)) ys₁
    map' {xs₁ = any xs₁} {ys₁ = any ys₁} {xs₁' = any xs₁'} {ys₁' = any ys₁'}
      refl refl fs₁ k
      | _ | [ refl ] | just _ | [ p₁ ] | just _ | [ q₁ ]
      with Vec.map-maybe (PartialFunctor.base H₂)
        (Vec.map (Functor.base F) xs₁)
      | inspect (Vec.map-maybe (PartialFunctor.base H₂))
        (Vec.map (Functor.base F) xs₁)
      | Vec.lookup-map-maybe' (PartialFunctor.base H₂)
        (Vec.map (Functor.base F) xs₁)
        (Vec.map (Functor.base G) xs₁')
        (base' xs₁ p₁)
      | Vec.map-maybe (PartialFunctor.base H₂)
        (Vec.map (Functor.base F) ys₁)
      | inspect (Vec.map-maybe (PartialFunctor.base H₂))
        (Vec.map (Functor.base F) ys₁)
      | Vec.lookup-map-maybe' (PartialFunctor.base H₂)
        (Vec.map (Functor.base F) ys₁)
        (Vec.map (Functor.base G) ys₁')
        (base' ys₁ q₁)
    ... | just _ | [ p₂ ] | refl | just _ | [ q₂ ] | refl
      with CategoryList.Arrow.lookup fs₁ k
    ... | nothing
      = CategoryList.nothing
    ... | just (l , f₁)
      = CategoryList.just l
      $ PartialFunctorSquare.map-arrow s
        (Vec.lookup-map (Functor.base F) xs₁ k)
        (Vec.lookup-map (Functor.base F) ys₁ l)
        (Vec.lookup-map (Functor.base G) xs₁' k)
        (Vec.lookup-map (Functor.base G) ys₁' l)
        (Vec.lookup-map-maybe (PartialFunctor.base H₁) xs₁ p₁ k)
        (Vec.lookup-map-maybe (PartialFunctor.base H₁) ys₁ q₁ l)
        (Vec.lookup-map-maybe (PartialFunctor.base H₂)
          (Vec.map (Functor.base F) xs₁) p₂ k)
        (Vec.lookup-map-maybe (PartialFunctor.base H₂)
          (Vec.map (Functor.base F) ys₁) q₂ l) f₁

    map
      : {xs₁ ys₁ : Category.Object (category-list C₁)}
      → {xs₁' ys₁' : Category.Object (category-list D₁)}
      → (p₁ : PartialFunctor.base (partial-functor-list H₁) xs₁ ≡ just xs₁')
      → (q₁ : PartialFunctor.base (partial-functor-list H₁) ys₁ ≡ just ys₁')
      → (fs₁ : Category.Arrow (category-list C₁) xs₁ ys₁)
      → Category.ArrowEqual (category-list D₂)
        (PartialFunctor.map
          (partial-functor-list H₂)
          (base xs₁ p₁)
          (base ys₁ q₁)
          (Functor.map (functor-list F) fs₁))
        (Functor.map (functor-list G)
          (PartialFunctor.map (partial-functor-list H₁) p₁ q₁ fs₁))
    map p₁ q₁ fs₁
      = record
      { lookup
        = map' p₁ q₁ fs₁
      }

  partial-functor-square-list
    : PartialFunctorSquare F G H₁ H₂
    → PartialFunctorSquare
      (functor-list F)
      (functor-list G)
      (partial-functor-list H₁)
      (partial-functor-list H₂)
  partial-functor-square-list s
    = record {PartialFunctorSquareList s}

