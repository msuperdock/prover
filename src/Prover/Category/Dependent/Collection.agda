module Prover.Category.Dependent.Collection where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor; ChainFunctorCompose; ChainFunctorEqual;
    ChainFunctorIdentity; ChainFunctorSquare)
open import Prover.Category.Collection
  using (category-collection; functor-collection; functor-compose-collection;
    functor-equal-collection; functor-identity-collection;
    functor-square-collection)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorEqual; DependentFunctorIdentity; DependentFunctorSquare)
open import Prover.Category.Dependent.Relation
  using (DependentInjective; DependentRelation)
open import Prover.Prelude

-- ## Types

-- ### DependentCategory

dependent-category-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentRelation C'
  → DependentCategory C

-- ### DependentFunctor

dependent-functor-collection
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {R : DependentRelation C'}
  → {S : DependentRelation D'}
  → {F : ChainFunctor C D}
  → {F' : DependentFunctor C' D' F}
  → DependentInjective R S F'
  → DependentFunctor
    (dependent-category-collection R)
    (dependent-category-collection S) F

-- ### DependentFunctorEqual

dependent-functor-equal-collection
  : {n : ℕ}
  → {C D : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {R : DependentRelation C'}
  → {S : DependentRelation D'}
  → {F₁ F₂ : ChainFunctor C D}
  → {F₁' : DependentFunctor C' D' F₁}
  → {F₂' : DependentFunctor C' D' F₂}
  → (i₁ : DependentInjective R S F₁')
  → (i₂ : DependentInjective R S F₂')
  → ChainFunctorEqual F₁ F₂
  → DependentFunctorEqual F₁' F₂'
  → DependentFunctorEqual
    (dependent-functor-collection i₁)
    (dependent-functor-collection i₂)

dependent-functor-equal-collection'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C : ChainCategory n}
  → (D : A → ChainCategory n)
  → {C' : DependentCategory C}
  → (D' : (x : A) → DependentCategory (D x))
  → {R : DependentRelation C'}
  → (S : (x : A) → DependentRelation (D' x))
  → {F₁ : ChainFunctor C (D x₁)}
  → {F₂ : ChainFunctor C (D x₂)}
  → {F₁' : DependentFunctor C' (D' x₁) F₁}
  → {F₂' : DependentFunctor C' (D' x₂) F₂}
  → (i₁ : DependentInjective R (S x₁) F₁')
  → (i₂ : DependentInjective R (S x₂) F₂')
  → x₁ ≡ x₂
  → ChainFunctorEqual F₁ F₂
  → DependentFunctorEqual F₁' F₂'
  → DependentFunctorEqual
    (dependent-functor-collection i₁)
    (dependent-functor-collection i₂)

-- ### DependentFunctorIdentity

dependent-functor-identity-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → {F : ChainFunctor C C}
  → {F' : DependentFunctor C' C' F}
  → (i : DependentInjective R R F')
  → ChainFunctorIdentity F
  → DependentFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-collection i)

dependent-functor-identity-collection'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → DependentCategory (C x))
  → (R : (x : A) → DependentRelation (C' x))
  → {F : ChainFunctor (C x₂) (C x₁)}
  → {F' : DependentFunctor (C' x₂) (C' x₁) F}
  → x₁ ≡ x₂
  → (i : DependentInjective (R x₂) (R x₁) F')
  → ChainFunctorIdentity F
  → DependentFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-collection i)

-- ### DependentFunctorCompose

dependent-functor-compose-collection
  : {n : ℕ}
  → {C D E : ChainCategory n}
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → {E' : DependentCategory E}
  → {R : DependentRelation C'}
  → {S : DependentRelation D'}
  → {T : DependentRelation E'}
  → {F : ChainFunctor D E}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C E}
  → {F' : DependentFunctor D' E' F}
  → {G' : DependentFunctor C' D' G}
  → {H' : DependentFunctor C' E' H}
  → (i : DependentInjective S T F')
  → (j : DependentInjective R S G')
  → (k : DependentInjective R T H')
  → ChainFunctorCompose F G H
  → DependentFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-collection i)
    (dependent-functor-collection j)
    (dependent-functor-collection k)

dependent-functor-compose-collection'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C D : ChainCategory n}
  → (E : A → ChainCategory n)
  → {C' : DependentCategory C}
  → {D' : DependentCategory D}
  → (E' : (x : A) → DependentCategory (E x))
  → {R : DependentRelation C'}
  → {S : DependentRelation D'}
  → (T : (x : A) → DependentRelation (E' x))
  → {F : ChainFunctor D (E x₂)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₁)}
  → {F' : DependentFunctor D' (E' x₂) F}
  → {G' : DependentFunctor C' D' G}
  → {H' : DependentFunctor C' (E' x₁) H}
  → x₁ ≡ x₂
  → (i : DependentInjective S (T x₂) F')
  → (j : DependentInjective R S G')
  → (k : DependentInjective R (T x₁) H')
  → ChainFunctorCompose F G H
  → DependentFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-collection i)
    (dependent-functor-collection j)
    (dependent-functor-collection k)

-- ### DependentFunctorSquare

dependent-functor-square-collection
  : {n : ℕ}
  → {C₁ C₂ D₁ D₂ : ChainCategory n}
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {D₁' : DependentCategory D₁}
  → {D₂' : DependentCategory D₂}
  → {R₁ : DependentRelation C₁'}
  → {R₂ : DependentRelation C₂'}
  → {S₁ : DependentRelation D₁'}
  → {S₂ : DependentRelation D₂'}
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ D₂}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ D₂}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' D₂' G}
  → {H₁' : DependentFunctor C₁' D₁' H₁}
  → {H₂' : DependentFunctor C₂' D₂' H₂}
  → (i : DependentInjective R₁ R₂ F')
  → (j : DependentInjective S₁ S₂ G')
  → (k₁ : DependentInjective R₁ S₁ H₁')
  → (k₂ : DependentInjective R₂ S₂ H₂')
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-collection i)
    (dependent-functor-collection j)
    (dependent-functor-collection k₁)
    (dependent-functor-collection k₂)

dependent-functor-square-collection'
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → {C₁ C₂ D₁ : ChainCategory n}
  → (D₂ : A → ChainCategory n)
  → {C₁' : DependentCategory C₁}
  → {C₂' : DependentCategory C₂}
  → {D₁' : DependentCategory D₁}
  → (D₂' : (x : A) → DependentCategory (D₂ x))
  → {R₁ : DependentRelation C₁'}
  → {R₂ : DependentRelation C₂'}
  → {S₁ : DependentRelation D₁'}
  → (S₂ : (x : A) → DependentRelation (D₂' x))
  → {F : ChainFunctor C₁ C₂}
  → {G : ChainFunctor D₁ (D₂ x₂)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₁)}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' (D₂' x₂) G}
  → {H₁' : DependentFunctor C₁' D₁' H₁}
  → {H₂' : DependentFunctor C₂' (D₂' x₁) H₂}
  → x₁ ≡ x₂
  → (i : DependentInjective R₁ R₂ F')
  → (j : DependentInjective S₁ (S₂ x₂) G')
  → (k₁ : DependentInjective R₁ S₁ H₁')
  → (k₂ : DependentInjective R₂ (S₂ x₁) H₂')
  → ChainFunctorSquare F G H₁ H₂
  → DependentFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-collection i)
    (dependent-functor-collection j)
    (dependent-functor-collection k₁)
    (dependent-functor-collection k₂)

-- ## Definitions

-- ### DependentCategory

dependent-category-collection {n = zero} {C' = C'} R
  = category-collection C' R

dependent-category-collection {n = suc _}
  {C = C} {C' = C'} R
  = record
  { category
    = λ x → dependent-category-collection
      (DependentRelation.relation R x)
  ; functor
    = λ f → dependent-functor-collection
      (DependentRelation.injective R f)
  ; functor-equal
    = λ {_} {_} {f₁} {f₂} p → dependent-functor-equal-collection
      (DependentRelation.injective R f₁)
      (DependentRelation.injective R f₂)
      (ChainCategory.functor-equal C p)
      (DependentCategory.functor-equal C' p)
  ; functor-identity
    = λ x → dependent-functor-identity-collection
      (DependentRelation.injective R (ChainCategory.identity C x))
      (ChainCategory.functor-identity C x)
      (DependentCategory.functor-identity C' x)
  ; functor-compose
    = λ f g → dependent-functor-compose-collection
      (DependentRelation.injective R f)
      (DependentRelation.injective R g)
      (DependentRelation.injective R (ChainCategory.compose C f g))
      (ChainCategory.functor-compose C f g)
      (DependentCategory.functor-compose C' f g)
  }

-- ### DependentFunctor

dependent-functor-collection {n = zero} {F' = F'} i
  = functor-collection F' i

dependent-functor-collection {n = suc _}
  {R = R} {S = S} {F = F} {F' = F'} i
  = record
  { functor
    = λ x → dependent-functor-collection
      (DependentInjective.injective i x)
  ; functor-square
    = λ {x = x} {y = y} f → dependent-functor-square-collection
      (DependentRelation.injective R f)
      (DependentRelation.injective S (ChainFunctor.map F f))
      (DependentInjective.injective i x)
      (DependentInjective.injective i y)
      (ChainFunctor.functor-square F f)
      (DependentFunctor.functor-square F' f)
  }

-- ### DependentFunctorEqual

dependent-functor-equal-collection {n = zero} i₁ i₂ _ p'
  = functor-equal-collection i₁ i₂ p'

dependent-functor-equal-collection {n = suc _}
  {D = D} {D' = D'} {S = S} i₁ i₂ p p'
  = record
  { functor
    = λ x → dependent-functor-equal-collection'
      (ChainCategory.category' D)
      (DependentCategory.category D')
      (DependentRelation.relation S)
      (DependentInjective.injective i₁ x)
      (DependentInjective.injective i₂ x)
      (ChainFunctorEqual.base p x)
      (ChainFunctorEqual.functor' p x)
      (DependentFunctorEqual.functor p' x)
  }

dependent-functor-equal-collection' _ _ _ i₁ i₂ refl
  = dependent-functor-equal-collection i₁ i₂

-- ### DependentFunctorIdentity

dependent-functor-identity-collection {n = zero} i _ p'
  = functor-identity-collection i p'

dependent-functor-identity-collection {n = suc _}
  {C = C} {C' = C'} {R = R} i p p'
  = record
  { functor
    = λ x → dependent-functor-identity-collection'
      (ChainCategory.category' C)
      (DependentCategory.category C')
      (DependentRelation.relation R)
      (ChainFunctorIdentity.base p x)
      (DependentInjective.injective i x)
      (ChainFunctorIdentity.functor' p x)
      (DependentFunctorIdentity.functor p' x)
  }

dependent-functor-identity-collection' _ _ _ refl
  = dependent-functor-identity-collection

-- ### DependentFunctorCompose

dependent-functor-compose-collection {n = zero} i j k _ p'
  = functor-compose-collection i j k p'

dependent-functor-compose-collection {n = suc _}
  {E = E} {E' = E'} {T = T} {G = G} i j k p p'
  = record
  { functor
    = λ x → dependent-functor-compose-collection'
      (ChainCategory.category' E)
      (DependentCategory.category E')
      (DependentRelation.relation T)
      (ChainFunctorCompose.base p x)
      (DependentInjective.injective i (ChainFunctor.base G x))
      (DependentInjective.injective j x)
      (DependentInjective.injective k x)
      (ChainFunctorCompose.functor' p x)
      (DependentFunctorCompose.functor p' x)
  }

dependent-functor-compose-collection' _ _ _ refl
  = dependent-functor-compose-collection

-- ### DependentFunctorSquare

dependent-functor-square-collection {n = zero} i j k₁ k₂ _ s'
  = functor-square-collection i j k₁ k₂ s'

dependent-functor-square-collection {n = suc _}
  {D₂ = D₂} {D₂' = D₂'} {S₂ = S₂} {F = F} {H₁ = H₁} i j k₁ k₂ s s'
  = record
  { functor
    = λ x₁ → dependent-functor-square-collection'
      (ChainCategory.category' D₂)
      (DependentCategory.category D₂')
      (DependentRelation.relation S₂)
      (ChainFunctorSquare.base s x₁)
      (DependentInjective.injective i x₁)
      (DependentInjective.injective j (ChainFunctor.base H₁ x₁))
      (DependentInjective.injective k₁ x₁)
      (DependentInjective.injective k₂ (ChainFunctor.base F x₁))
      (ChainFunctorSquare.functor' s x₁)
      (DependentFunctorSquare.functor s' x₁)
  }

dependent-functor-square-collection' _ _ _ refl
  = dependent-functor-square-collection

