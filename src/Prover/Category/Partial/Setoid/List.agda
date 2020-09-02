module Prover.Category.Partial.Setoid.List where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Category.Partial.Setoid
  using (PartialSetoidFunctor; PartialSetoidFunctorSquare)
open import Prover.Category.Setoid
  using (SetoidCategory; SetoidFunctor)
open import Prover.Category.Setoid.List
  using (module SetoidCategoryList; module SetoidFunctorList;
    setoid-category-list; setoid-functor-list)
open import Prover.Prelude

open List
  using (_!_)

-- ## PartialSetoidFunctor

module _
  {C D : Category}
  where

  module PartialSetoidFunctorList
    (F : PartialFunctor C D)
    where

    base
      : SetoidCategory.Object (setoid-category-list C)
      → Maybe (SetoidCategory.Object (setoid-category-list D))
    base
      = List.map-maybe
        (PartialFunctor.base F)

    map-lookup
      : {xs ys : SetoidCategory.Object (setoid-category-list C)}
      → {xs' ys' : SetoidCategory.Object (setoid-category-list D)}
      → base xs ≡ just xs'
      → base ys ≡ just ys'
      → SetoidCategory.Arrow (setoid-category-list C) xs ys
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
      with SetoidCategoryList.Arrow.lookup fs k
    ... | nothing
      = nothing
    ... | just (l , f)
      = just (l , PartialFunctor.map F
        (Vec.lookup-map-maybe (PartialFunctor.base F) xs p k)
        (Vec.lookup-map-maybe (PartialFunctor.base F) ys q l) f)

    abstract

      map-injective
        : {xs ys : SetoidCategory.Object (setoid-category-list C)}
        → {xs' ys' : SetoidCategory.Object (setoid-category-list D)}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → (f : SetoidCategory.Arrow (setoid-category-list C) xs ys)
        → (k₁ k₂ : Fin (List.length xs'))
        → {l : Fin (List.length ys')}
        → {f₁ : Category.Arrow D (xs' ! k₁) (ys' ! l)}
        → {f₂ : Category.Arrow D (xs' ! k₂) (ys' ! l)}
        → map-lookup p q f k₁ ≡ just (l , f₁)
        → map-lookup p q f k₂ ≡ just (l , f₂)
        → k₁ ≡ k₂
      map-injective {xs = any xs} {ys = any ys} _ _ _ _ _ _ _
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
        | Vec.map-maybe (PartialFunctor.base F) ys
        | inspect (Vec.map-maybe (PartialFunctor.base F)) ys
      map-injective refl refl f k₁ k₂ _ _
        | just _ | [ _ ] | just _ | [ _ ]
        with SetoidCategoryList.Arrow.lookup f k₁
        | inspect (SetoidCategoryList.Arrow.lookup f) k₁
        | SetoidCategoryList.Arrow.lookup f k₂
        | inspect (SetoidCategoryList.Arrow.lookup f) k₂
      map-injective _ _ f k₁ k₂ refl refl
        | _ | _ | _ | _ | just _ | [ p₁ ] | just _ | [ p₂ ]
        = SetoidCategoryList.Arrow.injective f k₁ k₂ p₁ p₂

    map
      : {xs ys : SetoidCategory.Object (setoid-category-list C)}
      → {xs' ys' : SetoidCategory.Object (setoid-category-list D)}
      → base xs ≡ just xs'
      → base ys ≡ just ys'
      → SetoidCategory.Arrow (setoid-category-list C) xs ys
      → SetoidCategory.Arrow (setoid-category-list D) xs' ys'
    map p q fs
      = record
      { lookup
        = map-lookup p q fs
      ; injective
        = map-injective p q fs
      }

    abstract

      map-eq'
        : {xs ys : SetoidCategory.Object (setoid-category-list C)}
        → {xs' ys' : SetoidCategory.Object (setoid-category-list D)}
        → {fs₁ fs₂ : SetoidCategory.Arrow (setoid-category-list C) xs ys}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → SetoidCategory.ArrowEqual (setoid-category-list C) fs₁ fs₂
        → (k : Fin (List.length xs'))
        → map-lookup p q fs₁ k ≡ map-lookup p q fs₂ k
      map-eq' {xs = any xs} {ys = any ys} _ _ _ _
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
        | Vec.map-maybe (PartialFunctor.base F) ys
        | inspect (Vec.map-maybe (PartialFunctor.base F)) ys
      map-eq' {fs₁ = fs₁} {fs₂ = fs₂} refl refl p k
        | just _ | [ _ ] | just _ | [ _ ]
        with SetoidCategoryList.Arrow.lookup fs₁ k
        | SetoidCategoryList.Arrow.lookup fs₂ k
        | SetoidCategoryList.ArrowEqual.lookup p k
      ... | _ | _ | refl
        = refl

      map-eq
        : {xs ys : SetoidCategory.Object (setoid-category-list C)}
        → {xs' ys' : SetoidCategory.Object (setoid-category-list D)}
        → {fs₁ fs₂ : SetoidCategory.Arrow (setoid-category-list C) xs ys}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → SetoidCategory.ArrowEqual (setoid-category-list C) fs₁ fs₂
        → SetoidCategory.ArrowEqual (setoid-category-list D)
          (map p q fs₁) (map p q fs₂)
      map-eq p q r
        = SetoidCategoryList.arrow-equal (map-eq' p q r)

      map-identity'
        : {xs' : SetoidCategory.Object (setoid-category-list D)}
        → (xs : SetoidCategory.Object (setoid-category-list C))
        → (p : base xs ≡ just xs')
        → (k : Fin (List.length xs'))
        → map-lookup p p (SetoidCategory.identity (setoid-category-list C) xs) k
          ≡ SetoidCategoryList.identity-lookup D xs' k
      map-identity' (any xs) _ _
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
      map-identity' (any xs) refl k
        | just _ | [ p ]
        = sub just
        $ Sigma.comma-eq refl
        $ PartialFunctor.map-identity F (Vec.lookup xs k)
          (Vec.lookup-map-maybe (PartialFunctor.base F) xs p k)

      map-identity
        : {xs' : SetoidCategory.Object (setoid-category-list D)}
        → (xs : SetoidCategory.Object (setoid-category-list C))
        → (p : base xs ≡ just xs')
        → SetoidCategory.ArrowEqual (setoid-category-list D)
          (map p p (SetoidCategory.identity (setoid-category-list C) xs))
          (SetoidCategory.identity (setoid-category-list D) xs')
      map-identity xs p
        = SetoidCategoryList.arrow-equal (map-identity' xs p)

      map-compose'
        : {xs ys zs : SetoidCategory.Object (setoid-category-list C)}
        → {xs' ys' zs' : SetoidCategory.Object (setoid-category-list D)}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → (r : base zs ≡ just zs')
        → (fs : SetoidCategory.Arrow (setoid-category-list C) ys zs)
        → (gs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
        → (k : Fin (List.length xs'))
        → map-lookup p r
          (SetoidCategory.compose (setoid-category-list C) fs gs) k
        ≡ SetoidCategoryList.compose-lookup D
          (map q r fs)
          (map p q gs) k
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
        | _ | _ | just _ | [ _ ] | just _ | [ _ ] | just _ | [ _ ]
        with SetoidCategoryList.Arrow.lookup gs k
      ... | nothing
        = refl

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
        | _ | _ | _ | _ | just _ | [ _ ] | just _ | [ _ ] | just _ | [ _ ]
        with SetoidCategoryList.Arrow.lookup gs k
      map-compose' _ _ _ fs _ _
        | _ | [ refl ] | _ | _ | _ | _ | _ | _ | _ | _ | just (l , _)
        with SetoidCategoryList.Arrow.lookup fs l
      ... | nothing
        = refl

      map-compose' {xs = any xs} {ys = any ys} {zs = any zs} _ _ _ _ _ _
        | _ | _ | just _ | [ _ ]
        with Vec.map-maybe (PartialFunctor.base F) xs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) xs
        | Vec.map-maybe (PartialFunctor.base F) ys
        | inspect (Vec.map-maybe (PartialFunctor.base F)) ys
        | Vec.map-maybe (PartialFunctor.base F) zs
        | inspect (Vec.map-maybe (PartialFunctor.base F)) zs
      map-compose' refl refl refl _ gs k
        | _ | _ | _ | _ | just _ | [ _ ] | just _ | [ _ ] | just _ | [ _ ]
        with SetoidCategoryList.Arrow.lookup gs k
      map-compose' _ _ _ fs _ _
        | _ | [ refl ] | _ | _ | _ | _ | _ | _ | _ | _ | just (l , _)
        with SetoidCategoryList.Arrow.lookup fs l
      map-compose' {xs = any xs} {ys = any ys} {zs = any zs} _ _ _ _ _ k
        | _ | _ | _ | [ refl ] | _ | [ p ] | _ | [ q ] | _ | [ r ]
        | just (l , g) | just (m , f)
        = sub just
        $ Sigma.comma-eq refl
        $ PartialFunctor.map-compose F
          (Vec.lookup-map-maybe (PartialFunctor.base F) xs p k)
          (Vec.lookup-map-maybe (PartialFunctor.base F) ys q l)
          (Vec.lookup-map-maybe (PartialFunctor.base F) zs r m) f g

      map-compose
        : {xs ys zs : SetoidCategory.Object (setoid-category-list C)}
        → {xs' ys' zs' : SetoidCategory.Object (setoid-category-list D)}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → (r : base zs ≡ just zs')
        → (fs : SetoidCategory.Arrow (setoid-category-list C) ys zs)
        → (gs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
        → SetoidCategory.ArrowEqual (setoid-category-list D)
          (map p r (SetoidCategory.compose (setoid-category-list C) fs gs))
          (SetoidCategory.compose (setoid-category-list D)
            (map q r fs) (map p q gs))
      map-compose p q r fs gs
        = SetoidCategoryList.arrow-equal (map-compose' p q r fs gs)

  partial-setoid-functor-list
    : PartialFunctor C D
    → PartialSetoidFunctor
      (setoid-category-list C)
      (setoid-category-list D)
  partial-setoid-functor-list F
    = record {PartialSetoidFunctorList F}

-- ## PartialSetoidFunctorSquare

module _
  {C₁ C₂ D₁ D₂ : Category}
  {F : Functor C₁ C₂}
  {G : Functor D₁ D₂}
  {H₁ : PartialFunctor C₁ D₁}
  {H₂ : PartialFunctor C₂ D₂}
  where

  module PartialSetoidFunctorSquareList
    (s : PartialFunctorSquare F G H₁ H₂)
    where

    base'
      : {n : ℕ}
      → {xs₁' : Vec (Category.Object D₁) n}
      → (xs₁ : Vec (Category.Object C₁) n)
      → Vec.map-maybe (PartialFunctor.base H₁) xs₁
        ≡ just xs₁'
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
      : {x₁' : SetoidCategory.Object (setoid-category-list D₁)}
      → (x₁ : SetoidCategory.Object (setoid-category-list C₁))
      → PartialSetoidFunctor.base (partial-setoid-functor-list H₁) x₁
        ≡ just x₁'
      → PartialSetoidFunctor.base (partial-setoid-functor-list H₂)
        (SetoidFunctor.base (setoid-functor-list F) x₁)
      ≡ just (SetoidFunctor.base (setoid-functor-list G) x₁')
    base (any xs₁) _
      with Vec.map-maybe (PartialFunctor.base H₁) xs₁
      | inspect (Vec.map-maybe (PartialFunctor.base H₁)) xs₁
    base {x₁' = any xs₁'} (any xs₁) refl | just _ | [ p₁ ]
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
      : {xs₁ ys₁ : SetoidCategory.Object (setoid-category-list C₁)}
      → {xs₁' ys₁' : SetoidCategory.Object (setoid-category-list D₁)}
      → (p₁ : PartialSetoidFunctor.base (partial-setoid-functor-list H₁) xs₁
        ≡ just xs₁')
      → (q₁ : PartialSetoidFunctor.base (partial-setoid-functor-list H₁) ys₁
        ≡ just ys₁')
      → (fs₁ : SetoidCategory.Arrow (setoid-category-list C₁) xs₁ ys₁)
      → (k : Fin (List.length xs₁'))
      → PartialSetoidFunctorList.map-lookup H₂ (base xs₁ p₁) (base ys₁ q₁)
        (SetoidFunctor.map (setoid-functor-list F) fs₁) k
      ≡ SetoidFunctorList.map-lookup G
        (PartialSetoidFunctor.map (partial-setoid-functor-list H₁) p₁ q₁ fs₁) k
    map' {xs₁ = any xs₁} {ys₁ = any ys₁} p₁ q₁ fs₁ _
      with PartialSetoidFunctor.map (partial-setoid-functor-list H₁) p₁ q₁ fs₁
      | inspect SetoidCategoryList.Arrow.lookup
        (PartialSetoidFunctor.map (partial-setoid-functor-list H₁) p₁ q₁ fs₁)
    ... | _ | _
      with Vec.map-maybe (PartialFunctor.base H₁) xs₁
      | inspect (Vec.map-maybe (PartialFunctor.base H₁)) xs₁
      | Vec.map-maybe (PartialFunctor.base H₁) ys₁
      | inspect (Vec.map-maybe (PartialFunctor.base H₁)) ys₁
    map' {xs₁ = any xs₁} {ys₁ = any ys₁} {xs₁' = any xs₁'} {ys₁' = any ys₁'}
      refl refl fs₁ k | _ | [ refl ] | just _ | [ p₁ ] | just _ | [ q₁ ]
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
      with SetoidCategoryList.Arrow.lookup fs₁ k
    ... | nothing
      = refl
    ... | just (l , f₁)
      = sub just
      $ Sigma.comma-eq refl
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
      : {xs₁ ys₁ : SetoidCategory.Object (setoid-category-list C₁)}
      → {xs₁' ys₁' : SetoidCategory.Object (setoid-category-list D₁)}
      → (p₁ : PartialSetoidFunctor.base (partial-setoid-functor-list H₁) xs₁
        ≡ just xs₁')
      → (q₁ : PartialSetoidFunctor.base (partial-setoid-functor-list H₁) ys₁
        ≡ just ys₁')
      → (fs₁ : SetoidCategory.Arrow (setoid-category-list C₁) xs₁ ys₁)
      → SetoidCategory.ArrowEqual (setoid-category-list D₂)
        (PartialSetoidFunctor.map (partial-setoid-functor-list H₂)
          (base xs₁ p₁)
          (base ys₁ q₁)
          (SetoidFunctor.map (setoid-functor-list F) fs₁))
        (SetoidFunctor.map (setoid-functor-list G)
          (PartialSetoidFunctor.map (partial-setoid-functor-list H₁) p₁ q₁ fs₁))
    map p₁ q₁ fs₁
      = SetoidCategoryList.arrow-equal (map' p₁ q₁ fs₁)

  partial-setoid-functor-square-list
    : PartialFunctorSquare F G H₁ H₂
    → PartialSetoidFunctorSquare
      (setoid-functor-list F)
      (setoid-functor-list G)
      (partial-setoid-functor-list H₁)
      (partial-setoid-functor-list H₂)
  partial-setoid-functor-square-list s
    = record {PartialSetoidFunctorSquareList s}

