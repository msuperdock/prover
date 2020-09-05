module Prover.Category.Dependent.Collection where

open import Prover.Category.Chain
  using (ChainCategory; ChainFunctor)
open import Prover.Category.Collection
  using (category-collection; functor-collection; functor-compose-collection;
    functor-identity-collection; functor-square-collection)
open import Prover.Category.Dependent
  using (DependentCategory; DependentFunctor; DependentFunctorCompose;
    DependentFunctorIdentity; DependentFunctorSquare; cons; dependent-category₀;
    dependent-functor₀; dependent-functor-compose₀; dependent-functor-identity₀;
    dependent-functor-square₀; nil)
open import Prover.Function.Dependent.Relation
  using (DependentInjective; DependentRelation; dependent-injective₀;
    dependent-relation₀)
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

-- ### DependentFunctorIdentity

dependent-functor-identity-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {R : DependentRelation C'}
  → {F : ChainFunctor C C}
  → {F' : DependentFunctor C' C' F}
  → (i : DependentInjective R R F')
  → DependentFunctorIdentity F'
  → DependentFunctorIdentity
    (dependent-functor-collection i)

dependent-functor-identity-collection-eq
  : {A : Set}
  → {x₁ x₂ : A}
  → {n : ℕ}
  → (C : A → ChainCategory n)
  → (C' : (x : A) → DependentCategory (C x))
  → (R : (x : A) → DependentRelation (C' x))
  → {F : ChainFunctor (C x₁) (C x₂)}
  → {F' : DependentFunctor (C' x₁) (C' x₂) F}
  → x₂ ≡ x₁
  → (i : DependentInjective (R x₁) (R x₂) F')
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
  → DependentFunctorCompose F' G' H'
  → DependentFunctorCompose
    (dependent-functor-collection i)
    (dependent-functor-collection j)
    (dependent-functor-collection k)

dependent-functor-compose-collection-eq
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
  → {F : ChainFunctor D (E x₁)}
  → {G : ChainFunctor C D}
  → {H : ChainFunctor C (E x₂)}
  → {F' : DependentFunctor D' (E' x₁) F}
  → {G' : DependentFunctor C' D' G}
  → {H' : DependentFunctor C' (E' x₂) H}
  → x₂ ≡ x₁
  → (i : DependentInjective S (T x₁) F')
  → (j : DependentInjective R S G')
  → (k : DependentInjective R (T x₂) H')
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
  → DependentFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-collection i)
    (dependent-functor-collection j)
    (dependent-functor-collection k₁)
    (dependent-functor-collection k₂)

dependent-functor-square-collection-eq
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
  → {G : ChainFunctor D₁ (D₂ x₁)}
  → {H₁ : ChainFunctor C₁ D₁}
  → {H₂ : ChainFunctor C₂ (D₂ x₂)}
  → {F' : DependentFunctor C₁' C₂' F}
  → {G' : DependentFunctor D₁' (D₂' x₁) G}
  → {H₁' : DependentFunctor C₁' D₁' H₁}
  → {H₂' : DependentFunctor C₂' (D₂' x₂) H₂}
  → x₂ ≡ x₁
  → (i : DependentInjective R₁ R₂ F')
  → (j : DependentInjective S₁ (S₂ x₁) G')
  → (k₁ : DependentInjective R₁ S₁ H₁')
  → (k₂ : DependentInjective R₂ (S₂ x₂) H₂')
  → DependentFunctorSquare F' G' H₁' H₂'
  → DependentFunctorSquare
    (dependent-functor-collection i)
    (dependent-functor-collection j)
    (dependent-functor-collection k₁)
    (dependent-functor-collection k₂)

-- ## Definitions

-- ### DependentCategory

dependent-category-collection
  {n = zero} {C' = C'} R
  = nil
    (category-collection
      (dependent-category₀ C')
      (dependent-relation₀ R))
dependent-category-collection
  {n = suc _} {C = C} {C' = C'} R
  = cons
    (λ x → dependent-category-collection
      (DependentRelation.tail R x))
    (λ f → dependent-functor-collection
      (DependentRelation.dependent-injective R f))
    (λ x → dependent-functor-identity-collection
      (DependentRelation.dependent-injective R (ChainCategory.identity C x))
      (DependentCategory.dependent-functor-identity C' x))
    (λ f g → dependent-functor-compose-collection
      (DependentRelation.dependent-injective R f)
      (DependentRelation.dependent-injective R g)
      (DependentRelation.dependent-injective R (ChainCategory.compose C f g))
      (DependentCategory.dependent-functor-compose C' f g))

-- ### DependentFunctor

dependent-functor-collection
  {n = zero} {R = R} {S = S} {F' = F'} i
  = nil
    (functor-collection
      (dependent-relation₀ R)
      (dependent-relation₀ S)
      (dependent-functor₀ F')
      (dependent-injective₀ i))
dependent-functor-collection
  {n = suc _} {R = R} {S = S} {F = F} {F' = F'} i
  = cons
    (λ x → dependent-functor-collection
      (DependentInjective.tail i x))
    (λ {x = x} {y = y} f → dependent-functor-square-collection
      (DependentRelation.dependent-injective R f)
      (DependentRelation.dependent-injective S (ChainFunctor.map F f))
      (DependentInjective.tail i x)
      (DependentInjective.tail i y)
      (DependentFunctor.dependent-functor-square F' f))

-- ### DependentFunctorIdentity

dependent-functor-identity-collection
  {n = zero} {R = R} i p
  = nil
    (functor-identity-collection
      (dependent-relation₀ R)
      (dependent-injective₀ i)
      (dependent-functor-identity₀ p))
dependent-functor-identity-collection
  {n = suc _} {C = C} {C' = C'} {R = R} i p
  = cons
    (DependentFunctorIdentity.head p)
    (λ x → dependent-functor-identity-collection-eq
      (ChainCategory.tail C)
      (DependentCategory.tail C')
      (DependentRelation.tail R)
      (DependentFunctorIdentity.base p x)
      (DependentInjective.tail i x)
      (DependentFunctorIdentity.tail p x))

dependent-functor-identity-collection-eq _ _ _ refl
  = dependent-functor-identity-collection

-- ### DependentFunctorCompose

dependent-functor-compose-collection
  {n = zero} {R = R} {S = S} {T = T} i j k p
  = nil
    (functor-compose-collection
      (dependent-relation₀ R)
      (dependent-relation₀ S)
      (dependent-relation₀ T)
      (dependent-injective₀ i)
      (dependent-injective₀ j)
      (dependent-injective₀ k)
      (dependent-functor-compose₀ p))
dependent-functor-compose-collection
  {n = suc _} {E = E} {E' = E'} {T = T} {G = G} i j k p
  = cons
    (DependentFunctorCompose.head p)
    (λ x → dependent-functor-compose-collection-eq
      (ChainCategory.tail E)
      (DependentCategory.tail E')
      (DependentRelation.tail T)
      (DependentFunctorCompose.base p x)
      (DependentInjective.tail i (ChainFunctor.base G x))
      (DependentInjective.tail j x)
      (DependentInjective.tail k x)
      (DependentFunctorCompose.tail p x))

dependent-functor-compose-collection-eq _ _ _ refl
  = dependent-functor-compose-collection

-- ### DependentFunctorSquare

dependent-functor-square-collection
  {n = zero} {R₁ = R₁} {R₂ = R₂} {S₁ = S₁} {S₂ = S₂} i j k₁ k₂ s
  = nil
    (functor-square-collection
      (dependent-relation₀ R₁)
      (dependent-relation₀ R₂)
      (dependent-relation₀ S₁)
      (dependent-relation₀ S₂)
      (dependent-injective₀ i)
      (dependent-injective₀ j)
      (dependent-injective₀ k₁)
      (dependent-injective₀ k₂)
      (dependent-functor-square₀ s))
dependent-functor-square-collection
  {n = suc _} {D₂ = D₂} {D₂' = D₂'} {S₂ = S₂} {F = F} {H₁ = H₁} i j k₁ k₂ s
  = cons
    (DependentFunctorSquare.head s)
    (λ x₁ → dependent-functor-square-collection-eq
      (ChainCategory.tail D₂)
      (DependentCategory.tail D₂')
      (DependentRelation.tail S₂)
      (DependentFunctorSquare.base s x₁)
      (DependentInjective.tail i x₁)
      (DependentInjective.tail j (ChainFunctor.base H₁ x₁))
      (DependentInjective.tail k₁ x₁)
      (DependentInjective.tail k₂ (ChainFunctor.base F x₁))
      (DependentFunctorSquare.tail s x₁))

dependent-functor-square-collection-eq _ _ _ refl
  = dependent-functor-square-collection

