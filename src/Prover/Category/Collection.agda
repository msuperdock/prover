module Prover.Category.Collection where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorIdentity; FunctorSquare)
open import Prover.Category.Induced
  using (category-induced; functor-compose-induced; functor-identity-induced;
    functor-induced; functor-induced'; functor-square-induced;
    functor-square-induced')
open import Prover.Category.List
  using (category-list; functor-compose-list; functor-identity-list;
    functor-list; functor-square-list)
open import Prover.Function
  using (FunctionInjective; function)
open import Prover.Function.Collection
  using (function-compose-collection; function-identity-collection;
    function-square-collection; function-square-collection')
open import Prover.Prelude

-- ## Category

category-collection
  : (C : Category)
  → Relation (Category.Object C)
  → Category
category-collection C R
  = category-induced
    (category-list C)
    (function (Collection.elements {R = R}))

-- ## Functor

functor-collection
  : {C D : Category}
  → {R : Relation (Category.Object C)}
  → {S : Relation (Category.Object D)}
  → (F : Functor C D)
  → FunctionInjective R S (Functor.function F)
  → Functor
    (category-collection C R)
    (category-collection D S)
functor-collection F i
  = functor-induced
    (functor-list F)
    (function-square-collection' i)

-- ## Functor'

functor-collection'
  : (C : Category)
  → (R : Relation (Category.Object C))
  → Functor
    (category-collection C R)
    (category-list C)
functor-collection' C R
  = functor-induced'
    (category-list C)
    (function (Collection.elements {R = R}))

-- ## FunctorIdentity

functor-identity-collection
  : {C : Category}
  → {R : Relation (Category.Object C)}
  → {F : Functor C C}
  → (i : FunctionInjective R R (Functor.function F))
  → FunctorIdentity F
  → FunctorIdentity
    (functor-collection F i)
functor-identity-collection i p
  = functor-identity-induced
    (function-square-collection' i)
    (function-identity-collection i (FunctorIdentity.function p))
    (functor-identity-list p)

-- ## FunctorCompose

functor-compose-collection
  : {C D E : Category}
  → {R : Relation (Category.Object C)}
  → {S : Relation (Category.Object D)}
  → {T : Relation (Category.Object E)}
  → {F : Functor D E}
  → {G : Functor C D}
  → {H : Functor C E}
  → (i : FunctionInjective S T (Functor.function F))
  → (j : FunctionInjective R S (Functor.function G))
  → (k : FunctionInjective R T (Functor.function H))
  → FunctorCompose F G H
  → FunctorCompose
    (functor-collection F i)
    (functor-collection G j)
    (functor-collection H k)
functor-compose-collection i j k p
  = functor-compose-induced
    (function-square-collection' i)
    (function-square-collection' j)
    (function-square-collection' k)
    (function-compose-collection i j k (FunctorCompose.function p))
    (functor-compose-list p)

-- ## FunctorSquare

functor-square-collection
  : {C₁ C₂ D₁ D₂ : Category}
  → {R₁ : Relation (Category.Object C₁)}
  → {R₂ : Relation (Category.Object C₂)}
  → {S₁ : Relation (Category.Object D₁)}
  → {S₂ : Relation (Category.Object D₂)}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → (i : FunctionInjective R₁ R₂ (Functor.function F))
  → (j : FunctionInjective S₁ S₂ (Functor.function G))
  → (k₁ : FunctionInjective R₁ S₁ (Functor.function H₁))
  → (k₂ : FunctionInjective R₂ S₂ (Functor.function H₂))
  → FunctorSquare F G H₁ H₂
  → FunctorSquare
    (functor-collection F i)
    (functor-collection G j)
    (functor-collection H₁ k₁)
    (functor-collection H₂ k₂)
functor-square-collection i j k₁ k₂ s
  = functor-square-induced
    (function-square-collection' i)
    (function-square-collection' j)
    (function-square-collection' k₁)
    (function-square-collection' k₂)
    (function-square-collection i j k₁ k₂ (FunctorSquare.function s))
    (functor-square-list s)

-- ## FunctorSquare'

module _
  {C₁ C₂ : Category}
  {R₁ : Relation (Category.Object C₁)}
  {R₂ : Relation (Category.Object C₂)}
  where

  functor-square-collection'
    : (F : Functor C₁ C₂)
    → (i : FunctionInjective R₁ R₂ (Functor.function F))
    → FunctorSquare
      (functor-collection F i)
      (functor-list F)
      (functor-collection' C₁ R₁)
      (functor-collection' C₂ R₂)
  functor-square-collection' F i
    = functor-square-induced'
      (functor-list F)
      (function-square-collection' i)

