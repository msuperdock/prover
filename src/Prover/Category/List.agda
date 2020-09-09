module Prover.Category.List where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Setoid
  using (SetoidCategory; category-setoid; functor-compose-setoid;
    functor-identity-setoid; functor-setoid; functor-square-setoid)
open import Prover.Category.Setoid.List
  using (module SetoidCategoryList; setoid-category-list;
    setoid-functor-compose-list; setoid-functor-identity-list;
    setoid-functor-list; setoid-functor-square-list)
open import Prover.Prelude

open List
  using ([]; _∷_; _!_)

-- ## Category

module CategoryList
  (C : Category)
  where

  open SetoidCategory (setoid-category-list C)
    using (Object)

  data Arrow'
    : Object
    → Object
    → Set
    where

    nil
      : {ys : Object}
      → Arrow' [] ys

    cons
      : {xs ys : Object}
      → (x : Category.Object C)
      → Maybe (l ∈ Fin (List.length ys)
        × Category.Arrow C x (ys ! l))
      → Arrow' xs ys
      → Arrow' (x ∷ xs) ys

  to-lookup
    : {xs ys : Object}
    → Arrow' xs ys
    → (k : Fin (List.length xs))
    → Maybe (l ∈ Fin (List.length ys)
      × Category.Arrow C (xs ! k) (ys ! l))
  to-lookup (cons _ f _) zero
    = f
  to-lookup (cons _ _ fs) (suc k)
    = to-lookup fs k

  record Arrow
    (xs ys : Object)
    : Set
    where

    field
    
      arrow'
        : Arrow' xs ys

    lookup
      : (k : Fin (List.length xs))
      → Maybe (l ∈ Fin (List.length ys)
        × Category.Arrow C (xs ! k) (ys ! l))
    lookup
      = to-lookup arrow'

    field

      .injective
        : (k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → {f₁ : Category.Arrow C (xs ! k₁) (ys ! l)}
        → {f₂ : Category.Arrow C (xs ! k₂) (ys ! l)}
        → lookup k₁ ≡ just (l , f₁)
        → lookup k₂ ≡ just (l , f₂)
        → k₁ ≡ k₂

    abstract

      injective'
        : (k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → {f₁ : Category.Arrow C (xs ! k₁) (ys ! l)}
        → {f₂ : Category.Arrow C (xs ! k₂) (ys ! l)}
        → lookup k₁ ≡ just (l , f₁)
        → lookup k₂ ≡ just (l , f₂)
        → k₁ ≡ k₂
      injective' k₁ k₂ p₁ p₂
        = Dec.recompute (k₁ ≟ k₂ fin) (injective k₁ k₂ p₁ p₂)

  arrow-eq
    : {xs ys : Object}
    → {fs₁ fs₂ : Arrow xs ys}
    → Arrow.arrow' fs₁ ≡ Arrow.arrow' fs₂
    → fs₁ ≡ fs₂
  arrow-eq refl
    = refl

  from-lookup
    : (xs ys : Object)
    → ((k : Fin (List.length xs))
      → Maybe (l ∈ Fin (List.length ys)
        × Category.Arrow C (xs ! k) (ys ! l)))
    → Arrow' xs ys
  from-lookup [] _ _
    = nil
  from-lookup (x ∷ xs) ys f
    = cons x (f zero) (from-lookup xs ys (f ∘ suc))

  from-lookup-eq
    : (xs ys : Object)
    → (f₁ f₂ : (k : Fin (List.length xs))
      → Maybe (l ∈ Fin (List.length ys)
        × Category.Arrow C (xs ! k) (ys ! l)))
    → ((k : Fin (List.length xs)) → f₁ k ≡ f₂ k)
    → from-lookup xs ys f₁ ≡ from-lookup xs ys f₂
  from-lookup-eq [] _ _ _ _
    = refl
  from-lookup-eq (_ ∷ xs) ys f₁ f₂ p
    with f₁ zero
    | p zero
    | from-lookup xs ys (f₁ ∘ suc)
    | from-lookup-eq xs ys (f₁ ∘ suc) (f₂ ∘ suc) (p ∘ suc)
  ... | _ | refl | _ | refl
    = refl

  from-to-lookup
    : {xs ys : Object}
    → (fs : Arrow' xs ys)
    → from-lookup xs ys (to-lookup fs) ≡ fs
  from-to-lookup nil
    = refl
  from-to-lookup (cons x f fs)
    = sub (cons x f) (from-to-lookup fs)

  to-from-lookup
    : (xs ys : Object)
    → (f : (k : Fin (List.length xs))
      → Maybe (l ∈ Fin (List.length ys)
        × Category.Arrow C (xs ! k) (ys ! l)))
    → (k : Fin (List.length xs))
    → to-lookup (from-lookup xs ys f) k ≡ f k
  to-from-lookup (_ ∷ _) _ _ zero
    = refl
  to-from-lookup (_ ∷ xs) ys f (suc k)
    = to-from-lookup xs ys (f ∘ suc) k

  to-setoid
    : {xs ys : Object}
    → Arrow xs ys
    → SetoidCategory.Arrow (setoid-category-list C) xs ys
  to-setoid fs
    = record
    { lookup
      = Arrow.lookup fs
    ; injective
      = Arrow.injective' fs
    }

  abstract

    from-injective
      : {xs ys : Object}
      → (fs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length ys)}
      → {f₁ : Category.Arrow C (xs ! k₁) (ys ! l)}
      → {f₂ : Category.Arrow C (xs ! k₂) (ys ! l)}
      → to-lookup (from-lookup xs ys (SetoidCategoryList.Arrow.lookup fs)) k₁
        ≡ just (l , f₁)
      → to-lookup (from-lookup xs ys (SetoidCategoryList.Arrow.lookup fs)) k₂
        ≡ just (l , f₂)
      → k₁ ≡ k₂
    from-injective {xs = xs} {ys = ys} fs k₁ k₂ p₁ p₂
      = SetoidCategoryList.Arrow.injective fs k₁ k₂
        (trans (sym (to-from-lookup xs ys
          (SetoidCategoryList.Arrow.lookup fs) k₁)) p₁)
        (trans (sym (to-from-lookup xs ys
          (SetoidCategoryList.Arrow.lookup fs) k₂)) p₂)

  from-setoid
    : {xs ys : Object}
    → SetoidCategory.Arrow (setoid-category-list C) xs ys
    → Arrow xs ys
  from-setoid {xs = xs} {ys = ys} fs
    = record
    { arrow'
      = from-lookup xs ys
        (SetoidCategoryList.Arrow.lookup fs)
    ; injective
      = from-injective fs
    }

  abstract

    from-setoid-eq
      : {xs ys : Object}
      → {fs₁ fs₂ : SetoidCategory.Arrow (setoid-category-list C) xs ys}
      → SetoidCategory.ArrowEqual (setoid-category-list C) fs₁ fs₂
      → from-setoid fs₁ ≡ from-setoid fs₂
    from-setoid-eq {xs = xs} {ys = ys} {fs₁ = fs₁} {fs₂ = fs₂} p
      = arrow-eq (from-lookup-eq xs ys
        (SetoidCategoryList.Arrow.lookup fs₁)
        (SetoidCategoryList.Arrow.lookup fs₂)
        (SetoidCategoryList.ArrowEqual.lookup p))

    from-to-setoid
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → from-setoid (to-setoid fs) ≡ fs
    from-to-setoid fs
      = arrow-eq (from-to-lookup (Arrow.arrow' fs))

    to-from-setoid
      : {xs ys : Object}
      → (fs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
      → SetoidCategory.ArrowEqual (setoid-category-list C)
        (to-setoid (from-setoid fs)) fs
    to-from-setoid {xs = xs} {ys = ys} fs
      = record
      { lookup
        = to-from-lookup xs ys
          (SetoidCategoryList.Arrow.lookup fs)
      }

  ArrowIsomorphism
    : (xs ys : List (Category.Object C))
    → SetoidIsomorphism
      (Arrow xs ys)
      (SetoidCategory.ArrowSetoid (setoid-category-list C) xs ys)
  ArrowIsomorphism _ _
    = record
    { to
      = to-setoid
    ; from
      = from-setoid
    ; from-eq
      = from-setoid-eq
    ; from-to
      = from-to-setoid
    ; to-from
      = to-from-setoid
    }

  update
    : {y : Category.Object C}
    → (xs : Object)
    → (k : Fin (List.length xs))
    → Category.Arrow C (xs ! k) y
    → Arrow xs (List.update xs k y)
  update xs k f
    = from-setoid (SetoidCategoryList.update C xs k f)

  insert
    : (xs : Object)
    → (k : Fin (suc (List.length xs)))
    → (y : Category.Object C)
    → Arrow xs (List.insert xs k y)
  insert xs k y
    = from-setoid (SetoidCategoryList.insert C xs k y)

  delete
    : (xs : Object)
    → (k : Fin (List.length xs))
    → Arrow xs (List.delete xs k)
  delete xs k
    = from-setoid (SetoidCategoryList.delete C xs k)

  swap
    : (x : Category.Object C)
    → (xs : Object)
    → (k : Fin (List.length xs))
    → Arrow (x ∷ xs) (List.swap x xs k)
  swap x xs k
    = from-setoid (SetoidCategoryList.swap C x xs k)

category-list
  : Category
  → Category
category-list C
  = category-setoid
    (setoid-category-list C)
    (CategoryList.Arrow C)
    (CategoryList.ArrowIsomorphism C)

-- ## Functor

functor-list
  : {C D : Category}
  → Functor C D
  → Functor
    (category-list C)
    (category-list D)
functor-list {C = C} {D = D} F
  = functor-setoid
    (CategoryList.Arrow C)
    (CategoryList.Arrow D)
    (CategoryList.ArrowIsomorphism C)
    (CategoryList.ArrowIsomorphism D)
    (setoid-functor-list F)

-- ## FunctorIdentity

functor-identity-list
  : {C : Category}
  → {F : Functor C C}
  → FunctorIdentity F
  → FunctorIdentity
    (functor-list F)
functor-identity-list {C = C} p
  = functor-identity-setoid
    (CategoryList.Arrow C)
    (CategoryList.ArrowIsomorphism C)
    (setoid-functor-identity-list p)

-- ## FunctorCompose

functor-compose-list
  : {C D E : Category}
  → {F : Functor D E}
  → {G : Functor C D}
  → {H : Functor C E}
  → FunctorCompose F G H
  → FunctorCompose
    (functor-list F)
    (functor-list G)
    (functor-list H)
functor-compose-list {C = C} {D = D} {E = E} p
  = functor-compose-setoid
    (CategoryList.Arrow C)
    (CategoryList.Arrow D)
    (CategoryList.Arrow E)
    (CategoryList.ArrowIsomorphism C)
    (CategoryList.ArrowIsomorphism D)
    (CategoryList.ArrowIsomorphism E)
    (setoid-functor-compose-list p)

-- ## FunctorSquare

functor-square-list
  : {C₁ C₂ D₁ D₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → FunctorSquare F G H₁ H₂
  → FunctorSquare
    (functor-list F)
    (functor-list G)
    (functor-list H₁)
    (functor-list H₂)
functor-square-list {C₁ = C₁} {C₂ = C₂} {D₁ = D₁} {D₂ = D₂} s
  = functor-square-setoid
    (CategoryList.Arrow C₁)
    (CategoryList.Arrow C₂)
    (CategoryList.Arrow D₁)
    (CategoryList.Arrow D₂)
    (CategoryList.ArrowIsomorphism C₁)
    (CategoryList.ArrowIsomorphism C₂)
    (CategoryList.ArrowIsomorphism D₁)
    (CategoryList.ArrowIsomorphism D₂)
    (setoid-functor-square-list s)

