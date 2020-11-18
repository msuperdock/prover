module Prover.Category.Partial.Collection.Unit where

open import Prover.Category
  using (Category; Functor)
open import Prover.Category.Collection.Unit
  using (category-collection-unit; functor-collection-unit)
open import Prover.Category.List.Unit
  using (category-list-unit; functor-list-unit)
open import Prover.Category.Partial
  using (PartialFunctor; PartialFunctorSquare)
open import Prover.Function.Relation
  using (FunctionInjective)
open import Prover.Function
  using (Function)
open import Prover.Prelude

-- ## PartialFunctor

module _
  {A : Set}
  where

  module PartialFunctorCollectionUnit
    (R : Relation A)
    (d : Decidable R)
    where

    base
      : Category.Object (category-list-unit A)
      → Maybe (Category.Object (category-collection-unit R))
    base
      = Collection.from-list R d

    map
      : {xs ys : Category.Object (category-list-unit A)}
      → {xs' ys' : Category.Object (category-collection-unit R)}
      → base xs ≡ just xs'
      → base ys ≡ just ys'
      → Category.Arrow (category-list-unit A) xs ys
      → Category.Arrow (category-collection-unit R) xs' ys'
    map {xs = xs} {ys = ys} _ _ _
      with Collection.from-list' R d xs
      | Collection.from-list' R d ys
    map refl refl fs | yes _ | yes _
      = record
      { elements
        = fs
      }

    abstract

      map-equal
        : {xs ys : Category.Object (category-list-unit A)}
        → {xs' ys' : Category.Object (category-collection-unit R)}
        → {fs₁ fs₂ : Category.Arrow (category-list-unit A) xs ys}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → Category.ArrowEqual (category-list-unit A) fs₁ fs₂
        → Category.ArrowEqual
          (category-collection-unit R)
          (map p q fs₁)
          (map p q fs₂)
      map-equal {xs = xs} {ys = ys} _ _ _
        with Collection.from-list' R d xs
        | Collection.from-list' R d ys
      map-equal refl refl ps | yes _ | yes _
        = record
        { elements
          = ps
        }

      map-identity
        : {xs' : Category.Object (category-collection-unit R)}
        → (xs : Category.Object (category-list-unit A))
        → (p : base xs ≡ just xs')
        → Category.ArrowEqual
          (category-collection-unit R)
          (map p p (Category.identity (category-list-unit A) xs))
          (Category.identity (category-collection-unit R) xs')
      map-identity xs _
        with Collection.from-list' R d xs
      map-identity _ refl | yes _
        = record
        { elements
          = Category.arrow-refl (category-list-unit A)
        }

      map-compose
        : {xs ys zs : Category.Object (category-list-unit A)}
        → {xs' ys' zs' : Category.Object (category-collection-unit R)}
        → (p : base xs ≡ just xs')
        → (q : base ys ≡ just ys')
        → (r : base zs ≡ just zs')
        → (fs : Category.Arrow (category-list-unit A) ys zs)
        → (gs : Category.Arrow (category-list-unit A) xs ys)
        → Category.ArrowEqual
          (category-collection-unit R)
          (map p r (Category.compose (category-list-unit A) fs gs))
          (Category.compose (category-collection-unit R)
            (map q r fs)
            (map p q gs))
      map-compose {xs = xs} {ys = ys} {zs = zs} _ _ _ _ _
        with Collection.from-list' R d xs
        | Collection.from-list' R d ys
        | Collection.from-list' R d zs
      map-compose refl refl refl _ _ | yes _ | yes _ | yes _
        = record
        { elements
          = Category.arrow-refl (category-list-unit A)
        }

  partial-functor-collection-unit
    : (R : Relation A)
    → Decidable R
    → PartialFunctor
      (category-list-unit A)
      (category-collection-unit R)
  partial-functor-collection-unit R d
    = record {PartialFunctorCollectionUnit R d}

-- ## PartialFunctorSquare

module _
  {A₁ A₂ : Set}
  {R₁ : Relation A₁}
  {R₂ : Relation A₂}
  where

  module PartialFunctorSquareCollectionUnit
    (d₁ : Decidable R₁)
    (d₂ : Decidable R₂)
    {F : Function A₁ A₂}
    (i : FunctionInjective R₁ R₂ F)
    where

    base
      : {xs₁' : Category.Object (category-collection-unit R₁)}
      → (xs₁ : Category.Object (category-list-unit A₁))
      → PartialFunctor.base (partial-functor-collection-unit R₁ d₁) xs₁
        ≡ just xs₁'
      → PartialFunctor.base (partial-functor-collection-unit R₂ d₂)
        (Functor.base (functor-list-unit F) xs₁)
      ≡ just (Functor.base (functor-collection-unit i) xs₁')
    base xs₁ _
      with Collection.from-list' R₁ d₁ xs₁
      | Collection.from-list' R₂ d₂ (List.map (Function.base F) xs₁)
    base {xs₁' = xs₁'} _ refl | yes _ | no ¬p₂
      = ⊥-elim (¬p₂ (Collection.valid'
        (Collection.map R₂ (Function.base F) (FunctionInjective.base i) xs₁')))
    base _ refl | yes _ | yes _
      = refl

    map
      : {xs₁ ys₁ : Category.Object (category-list-unit A₁)}
      → {xs₁' ys₁' : Category.Object (category-collection-unit R₁)}
      → (p₁ : PartialFunctor.base (partial-functor-collection-unit R₁ d₁) xs₁
        ≡ just xs₁')
      → (q₁ : PartialFunctor.base (partial-functor-collection-unit R₁ d₁) ys₁
        ≡ just ys₁')
      → (fs₁ : Category.Arrow (category-list-unit A₁) xs₁ ys₁)
      → Category.ArrowEqual
        (category-collection-unit R₂)
        (PartialFunctor.map (partial-functor-collection-unit R₂ d₂)
          (base xs₁ p₁)
          (base ys₁ q₁)
          (Functor.map (functor-list-unit F) fs₁))
        (Functor.map (functor-collection-unit i)
          (PartialFunctor.map
            (partial-functor-collection-unit R₁ d₁) p₁ q₁ fs₁))
    map {xs₁ = xs₁} {ys₁ = ys₁} _ _ _
      with Collection.from-list' R₁ d₁ xs₁
      | Collection.from-list' R₂ d₂ (List.map (Function.base F) xs₁)
      | Collection.from-list' R₁ d₁ ys₁
      | Collection.from-list' R₂ d₂ (List.map (Function.base F) ys₁)
    map {xs₁' = xs₁'} refl _ _ | yes _ | no ¬p₂ | _ | _
      = ⊥-elim (¬p₂ (Collection.valid'
        (Collection.map R₂ (Function.base F) (FunctionInjective.base i) xs₁')))
    map {ys₁' = ys₁'} _ refl _ | _ | _ | yes _ | no ¬q₂
      = ⊥-elim (¬q₂ (Collection.valid'
        (Collection.map R₂ (Function.base F) (FunctionInjective.base i) ys₁')))
    map refl refl _ | yes _ | yes _ | yes _ | yes _
      = record
      { elements
        = Category.arrow-refl (category-list-unit A₂)
      }

  partial-functor-square-collection-unit
    : (d₁ : Decidable R₁)
    → (d₂ : Decidable R₂)
    → {F : Function A₁ A₂}
    → (i : FunctionInjective R₁ R₂ F)
    → PartialFunctorSquare
      (functor-list-unit F)
      (functor-collection-unit i)
      (partial-functor-collection-unit R₁ d₁)
      (partial-functor-collection-unit R₂ d₂)
  partial-functor-square-collection-unit d₁ d₂ i
    = record {PartialFunctorSquareCollectionUnit d₁ d₂ i}

