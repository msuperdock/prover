module Prover.Category.Dependent.Collection.Unit where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorEqual;
    ChainFunctorIdentity; ChainFunctorSquare)
open import Prover.Category.Collection.Unit
  using (category-collection-unit; functor-collection-unit;
    functor-compose-collection-unit; functor-equal-collection-unit;
    functor-identity-collection-unit; functor-square-collection-unit)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorEqual; DependentFunctorIdentity; DependentFunctorSquare)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; DependentSimpleFunctor;
    DependentSimpleFunctorCompose; DependentSimpleFunctorEqual;
    DependentSimpleFunctorIdentity; DependentSimpleFunctorSquare)
open import Prover.Category.Dependent.Simple.Relation
  using (DependentSimpleInjective; DependentSimpleRelation)
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

dependent-category-collection-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleRelation C'
  → DependentCategory C

-- ### DependentFunctor

dependent-functor-collection-unit
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {R : DependentSimpleRelation C'}
  → {S : DependentSimpleRelation D'}
  → {F : ChainFunctor C D}
  → {F' : DependentSimpleFunctor C' D' F}
  → DependentSimpleInjective R S F'
  → DependentFunctor
    (dependent-category-collection-unit R)
    (dependent-category-collection-unit S) F

-- ### DependentFunctorEqual

dependent-functor-equal-collection-unit
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {R : DependentSimpleRelation C'}
  → {S : DependentSimpleRelation D'}
  → {F₁ F₂ : ChainFunctor C D}
  → {F₁' : DependentSimpleFunctor C' D' F₁}
  → {F₂' : DependentSimpleFunctor C' D' F₂}
  → (i₁ : DependentSimpleInjective R S F₁')
  → (i₂ : DependentSimpleInjective R S F₂')
  → ChainFunctorEqual F₁ F₂
  → DependentSimpleFunctorEqual F₁' F₂'
  → DependentFunctorEqual
    (dependent-functor-collection-unit i₁)
    (dependent-functor-collection-unit i₂)

dependent-functor-equal-collection-unit'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C : ChainCategory n}
  → (D : A → ChainCategory n)
  → {C' : DependentSimpleCategory C}
  → (D' : (x : A) → DependentSimpleCategory (D x))
  → {R : DependentSimpleRelation C'}
  → (S : (x : A) → DependentSimpleRelation (D' x))
  → {F₁ : ChainFunctor C (D x₁)}
  → {F₂ : ChainFunctor C (D x₂)}
  → {F₁' : DependentSimpleFunctor C' (D' x₁) F₁}
  → {F₂' : DependentSimpleFunctor C' (D' x₂) F₂}
  → (i₁ : DependentSimpleInjective R (S x₁) F₁')
  → (i₂ : DependentSimpleInjective R (S x₂) F₂')
  → x₁ ≡ x₂
  → ChainFunctorEqual F₁ F₂
  → DependentSimpleFunctorEqual F₁' F₂'
  → DependentFunctorEqual
    (dependent-functor-collection-unit i₁)
    (dependent-functor-collection-unit i₂)

-- ### DependentFunctorIdentity

dependent-functor-identity-collection-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → {F : ChainFunctor C C}
  → {F' : DependentSimpleFunctor C' C' F}
  → (i : DependentSimpleInjective R R F')
  → ChainFunctorIdentity F
  → DependentSimpleFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-collection-unit i)

dependent-functor-identity-collection-unit'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → DependentSimpleCategory (C x))
  → (R : (x : A) → DependentSimpleRelation (C' x))
  → {F : ChainFunctor (C x₂) (C x₁)}
  → {F' : DependentSimpleFunctor (C' x₂) (C' x₁) F}
  → x₁ ≡ x₂
  → (i : DependentSimpleInjective (R x₂) (R x₁) F')
  → ChainFunctorIdentity F
  → DependentSimpleFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-collection-unit i)

-- ### DependentFunctorCompose

dependent-functor-compose-collection-unit
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → {E' : DependentSimpleCategory E}
  → {R : DependentSimpleRelation C'}
  → {S : DependentSimpleRelation D'}
  → {T : DependentSimpleRelation E'}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : DependentSimpleFunctor D' E' F}
  → {G' : DependentSimpleFunctor C' D' G}
  → {H' : DependentSimpleFunctor C' E' H}
  → (i : DependentSimpleInjective S T F')
  → (j : DependentSimpleInjective R S G')
  → (k : DependentSimpleInjective R T H')
  → ChainFunctorCompose F G H
  → DependentSimpleFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-collection-unit i)
    (dependent-functor-collection-unit j)
    (dependent-functor-collection-unit k)

dependent-functor-compose-collection-unit'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSimpleCategory D}
  → (E' : (x : A) → DependentSimpleCategory (E x))
  → {R : DependentSimpleRelation C'}
  → {S : DependentSimpleRelation D'}
  → (T : (x : A) → DependentSimpleRelation (E' x))
  → {F : ChainFunctor D (E x₂)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₁)}
  → {F' : DependentSimpleFunctor D' (E' x₂) F}
  → {G' : DependentSimpleFunctor C' D' G}
  → {H' : DependentSimpleFunctor C' (E' x₁) H}
  → x₁ ≡ x₂
  → (i : DependentSimpleInjective S (T x₂) F')
  → (j : DependentSimpleInjective R S G')
  → (k : DependentSimpleInjective R (T x₁) H')
  → ChainFunctorCompose F G H
  → DependentSimpleFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-collection-unit i)
    (dependent-functor-collection-unit j)
    (dependent-functor-collection-unit k)

-- ### DependentFunctorSquare

dependent-functor-square-collection-unit
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {D₁' : DependentSimpleCategory D₁}
  → {D₂' : DependentSimpleCategory D₂}
  → {R₁ : DependentSimpleRelation C₁'}
  → {R₂ : DependentSimpleRelation C₂'}
  → {S₁ : DependentSimpleRelation D₁'}
  → {S₂ : DependentSimpleRelation D₂'}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : DependentSimpleFunctor C₁' C₂' F}
  → {G' : DependentSimpleFunctor D₁' D₂' G}
  → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
  → {H₂' : DependentSimpleFunctor C₂' D₂' H₂}
  → (i : DependentSimpleInjective R₁ R₂ F')
  → (j : DependentSimpleInjective S₁ S₂ G')
  → (k₁ : DependentSimpleInjective R₁ S₁ H₁')
  → (k₂ : DependentSimpleInjective R₂ S₂ H₂')
  → ChainFunctorSquare F G H₁ H₂
  → DependentSimpleFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-collection-unit i)
    (dependent-functor-collection-unit j)
    (dependent-functor-collection-unit k₁)
    (dependent-functor-collection-unit k₂)

dependent-functor-square-collection-unit'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁' : DependentSimpleCategory C₁}
  → {C₂' : DependentSimpleCategory C₂}
  → {D₁' : DependentSimpleCategory D₁}
  → (D₂' : (x : A) → DependentSimpleCategory (D₂ x))
  → {R₁ : DependentSimpleRelation C₁'}
  → {R₂ : DependentSimpleRelation C₂'}
  → {S₁ : DependentSimpleRelation D₁'}
  → (S₂ : (x : A) → DependentSimpleRelation (D₂' x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₂)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₁)}
  → {F' : DependentSimpleFunctor C₁' C₂' F}
  → {G' : DependentSimpleFunctor D₁' (D₂' x₂) G}
  → {H₁' : DependentSimpleFunctor C₁' D₁' H₁}
  → {H₂' : DependentSimpleFunctor C₂' (D₂' x₁) H₂}
  → x₁ ≡ x₂
  → (i : DependentSimpleInjective R₁ R₂ F')
  → (j : DependentSimpleInjective S₁ (S₂ x₂) G')
  → (k₁ : DependentSimpleInjective R₁ S₁ H₁')
  → (k₂ : DependentSimpleInjective R₂ (S₂ x₁) H₂')
  → ChainFunctorSquare F G H₁ H₂
  → DependentSimpleFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-collection-unit i)
    (dependent-functor-collection-unit j)
    (dependent-functor-collection-unit k₁)
    (dependent-functor-collection-unit k₂)

-- ## Definitions

-- ### DependentCategory

dependent-category-collection-unit {n = zero} R
  = category-collection-unit R

dependent-category-collection-unit {n = suc _}
  {C = C} {C' = C'} R
  = record
  { category
    = λ x → dependent-category-collection-unit
      (DependentSimpleRelation.relation R x)
  ; functor
    = λ f → dependent-functor-collection-unit
      (DependentSimpleRelation.injective R f)
  ; functor-equal
    = λ {_} {_} {f₁} {f₂} p → dependent-functor-equal-collection-unit
      (DependentSimpleRelation.injective R f₁)
      (DependentSimpleRelation.injective R f₂)
      (ChainCategory.functor-equal C p)
      (DependentSimpleCategory.functor-equal C' p)
  ; functor-identity
    = λ x → dependent-functor-identity-collection-unit
      (DependentSimpleRelation.injective R (ChainCategory.identity C x))
      (ChainCategory.functor-identity C x)
      (DependentSimpleCategory.functor-identity C' x)
  ; functor-compose
    = λ f g → dependent-functor-compose-collection-unit
      (DependentSimpleRelation.injective R f)
      (DependentSimpleRelation.injective R g)
      (DependentSimpleRelation.injective R (ChainCategory.compose C f g))
      (ChainCategory.functor-compose C f g)
      (DependentSimpleCategory.functor-compose C' f g)
  }

-- ### DependentFunctor

dependent-functor-collection-unit {n = zero} i
  = functor-collection-unit i

dependent-functor-collection-unit {n = suc _}
  {R = R} {S = S} {F = F} {F' = F'} i
  = record
  { functor
    = λ x → dependent-functor-collection-unit
      (DependentSimpleInjective.injective i x)
  ; functor-square
    = λ {x = x} {y = y} f → dependent-functor-square-collection-unit
      (DependentSimpleRelation.injective R f)
      (DependentSimpleRelation.injective S (ChainFunctor.map F f))
      (DependentSimpleInjective.injective i x)
      (DependentSimpleInjective.injective i y)
      (ChainFunctor.functor-square F f)
      (DependentSimpleFunctor.functor-square F' f)
  }

-- ### DependentFunctorEqual

dependent-functor-equal-collection-unit {n = zero} i₁ i₂ _ p'
  = functor-equal-collection-unit i₁ i₂ p'

dependent-functor-equal-collection-unit {n = suc _}
  {D = D} {D' = D'} {S = S} i₁ i₂ p p'
  = record
  { functor
    = λ x → dependent-functor-equal-collection-unit'
      (ChainCategory.category' D)
      (DependentSimpleCategory.category D')
      (DependentSimpleRelation.relation S)
      (DependentSimpleInjective.injective i₁ x)
      (DependentSimpleInjective.injective i₂ x)
      (ChainFunctorEqual.base p x)
      (ChainFunctorEqual.functor' p x)
      (DependentSimpleFunctorEqual.functor p' x)
  }

dependent-functor-equal-collection-unit' _ _ _ i₁ i₂ refl
  = dependent-functor-equal-collection-unit i₁ i₂

-- ### DependentFunctorIdentity

dependent-functor-identity-collection-unit {n = zero} i _ p'
  = functor-identity-collection-unit i p'

dependent-functor-identity-collection-unit {n = suc _}
  {C = C} {C' = C'} {R = R} i p p'
  = record
  { functor
    = λ x → dependent-functor-identity-collection-unit'
      (ChainCategory.category' C)
      (DependentSimpleCategory.category C')
      (DependentSimpleRelation.relation R)
      (ChainFunctorIdentity.base p x)
      (DependentSimpleInjective.injective i x)
      (ChainFunctorIdentity.functor' p x)
      (DependentSimpleFunctorIdentity.functor p' x)
  }

dependent-functor-identity-collection-unit' _ _ _ refl
  = dependent-functor-identity-collection-unit

-- ### DependentFunctorCompose

dependent-functor-compose-collection-unit {n = zero} i j k _ p'
  = functor-compose-collection-unit i j k p'

dependent-functor-compose-collection-unit {n = suc _}
  {E = E} {E' = E'} {T = T} {G = G} i j k p p'
  = record
  { functor
    = λ x → dependent-functor-compose-collection-unit'
      (ChainCategory.category' E)
      (DependentSimpleCategory.category E')
      (DependentSimpleRelation.relation T)
      (ChainFunctorCompose.base p x)
      (DependentSimpleInjective.injective i (ChainFunctor.base G x))
      (DependentSimpleInjective.injective j x)
      (DependentSimpleInjective.injective k x)
      (ChainFunctorCompose.functor' p x)
      (DependentSimpleFunctorCompose.functor p' x)
  }

dependent-functor-compose-collection-unit' _ _ _ refl
  = dependent-functor-compose-collection-unit

-- ### DependentFunctorSquare

dependent-functor-square-collection-unit {n = zero} i j k₁ k₂ _ s'
  = functor-square-collection-unit i j k₁ k₂ s'

dependent-functor-square-collection-unit {n = suc _}
  {D₂ = D₂} {D₂' = D₂'} {S₂ = S₂} {F = F} {H₁ = H₁} i j k₁ k₂ s s'
  = record
  { functor
    = λ x₁ → dependent-functor-square-collection-unit'
      (ChainCategory.category' D₂)
      (DependentSimpleCategory.category D₂')
      (DependentSimpleRelation.relation S₂)
      (ChainFunctorSquare.base s x₁)
      (DependentSimpleInjective.injective i x₁)
      (DependentSimpleInjective.injective j (ChainFunctor.base H₁ x₁))
      (DependentSimpleInjective.injective k₁ x₁)
      (DependentSimpleInjective.injective k₂ (ChainFunctor.base F x₁))
      (ChainFunctorSquare.functor' s x₁)
      (DependentSimpleFunctorSquare.functor s' x₁)
  }

dependent-functor-square-collection-unit' _ _ _ refl
  = dependent-functor-square-collection-unit

