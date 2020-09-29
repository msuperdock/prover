module Prover.Function.Collection where

open import Prover.Function
  using (Function; FunctionCompose; FunctionIdentity; FunctionSquare; function)
open import Prover.Function.List
  using (function-compose-list; function-identity-list; function-list;
    function-square-list)
open import Prover.Function.Relation
  using (FunctionInjective)
open import Prover.Prelude

-- ## Function

module _
  {A B : Set}
  {R : Relation A}
  {S : Relation B}
  {F : Function A B}
  where

  module FunctionCollection
    (i : FunctionInjective R S F)
    where

    base
      : Collection R
      → Collection S
    base
      = Collection.map S
        (Function.base F)
        (FunctionInjective.base i)

  function-collection
    : FunctionInjective R S F
    → Function (Collection R) (Collection S)
  function-collection i
    = record {FunctionCollection i}

-- ## FunctionIdentity

module _
  {A : Set}
  {R : Relation A}
  {F : Function A A}
  where

  module FunctionIdentityCollection
    (i : FunctionInjective R R F)
    (p : FunctionIdentity F)
    where

    base
      : (xs : Collection R)
      → Function.base (function-collection i) xs ≅ xs
    base (collection xs _)
      = collection-eq
      $ FunctionIdentity.base
        (function-identity-list p) xs

  function-identity-collection
    : (i : FunctionInjective R R F)
    → FunctionIdentity F
    → FunctionIdentity
      (function-collection i)
  function-identity-collection i p
    = record {FunctionIdentityCollection i p}

-- ## FunctionCompose

module _
  {A B C : Set}
  {R : Relation A}
  {S : Relation B}
  {T : Relation C}
  {F : Function B C}
  {G : Function A B}
  {H : Function A C}
  where

  module FunctionComposeCollection
    (i : FunctionInjective S T F)
    (j : FunctionInjective R S G)
    (k : FunctionInjective R T H)
    (p : FunctionCompose F G H)
    where

    base
      : (xs : Collection R)
      → Function.base (function-collection k) xs
      ≅ Function.base (function-collection i)
        (Function.base (function-collection j) xs)
    base (collection xs _)
      = collection-eq
      $ FunctionCompose.base
        (function-compose-list p) xs

  function-compose-collection
    : (i : FunctionInjective S T F)
    → (j : FunctionInjective R S G)
    → (k : FunctionInjective R T H)
    → FunctionCompose F G H
    → FunctionCompose
      (function-collection i)
      (function-collection j)
      (function-collection k)
  function-compose-collection i j k p
    = record {FunctionComposeCollection i j k p}

-- ## FunctionSquare

module _
  {A₁ A₂ B₁ B₂ : Set}
  {R₁ : Relation A₁}
  {R₂ : Relation A₂}
  {S₁ : Relation B₁}
  {S₂ : Relation B₂}
  {F : Function A₁ A₂}
  {G : Function B₁ B₂}
  {H₁ : Function A₁ B₁}
  {H₂ : Function A₂ B₂}
  where

  module FunctionSquareCollection
    (i : FunctionInjective R₁ R₂ F)
    (j : FunctionInjective S₁ S₂ G)
    (k₁ : FunctionInjective R₁ S₁ H₁)
    (k₂ : FunctionInjective R₂ S₂ H₂)
    (s : FunctionSquare F G H₁ H₂)
    where

    base
      : (xs₁ : Collection R₁)
      → Function.base (function-collection k₂)
        (Function.base (function-collection i) xs₁)
      ≅ Function.base (function-collection j)
        (Function.base (function-collection k₁) xs₁)
    base (collection xs₁ _)
      = collection-eq
      $ FunctionSquare.base
        (function-square-list s) xs₁

  function-square-collection
    : (i : FunctionInjective R₁ R₂ F)
    → (j : FunctionInjective S₁ S₂ G)
    → (k₁ : FunctionInjective R₁ S₁ H₁)
    → (k₂ : FunctionInjective R₂ S₂ H₂)
    → FunctionSquare F G H₁ H₂
    → FunctionSquare
      (function-collection i)
      (function-collection j)
      (function-collection k₁)
      (function-collection k₂)
  function-square-collection i j k₁ k₂ s
    = record {FunctionSquareCollection i j k₁ k₂ s}

-- ## FunctionSquare'

module _
  {A B : Set}
  {R : Relation A}
  {S : Relation B}
  {F : Function A B}
  where

  module FunctionSquareCollection'
    (i : FunctionInjective R S F)
    where

    base
      : (xs : Collection R)
      → Function.base (function-list F)
        (Function.base (function Collection.elements) xs)
      ≅ Function.base (function Collection.elements)
        (Function.base (function-collection i) xs)
    base _
      = refl

  function-square-collection'
    : (i : FunctionInjective R S F)
    → FunctionSquare
      (function Collection.elements)
      (function Collection.elements)
      (function-collection i)
      (function-list F)
  function-square-collection' i
    = record {FunctionSquareCollection' i}

