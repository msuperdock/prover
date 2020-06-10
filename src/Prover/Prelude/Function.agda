module Prover.Prelude.Function where

open import Prover.Prelude.Level
  using (Level)

infixr -1 _$_

_$_
  : {a b : Level}
  → {A : Set a}
  → {B : A → Set b}
  → ((x : A) → B x)
  → ((x : A) → B x)
f $ x
  = f x

infixr 9 _∘_

_∘_
  : {a b c : Level}
  → {A : Set a}
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
  → ({x : A} → (y : B x) → C y)
  → (g : (x : A) → B x)
  → ((x : A) → C (g x))
f ∘ g
  = λ x → f (g x)

id
  : {a : Level}
  → {A : Set a}
  → A
  → A
id x
  = x

const
  : {a b : Level}
  → {A : Set a}
  → {B : Set b}
  → A
  → B
  → A
const x y
  = x

