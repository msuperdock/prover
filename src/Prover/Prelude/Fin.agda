module Prover.Prelude.Fin where

open import Prover.Prelude.Decidable
  using (Decidable; no; yes)
open import Prover.Prelude.Equality
  using (_≡_; _≢_; refl; sub)
open import Prover.Prelude.Function
  using (id)
open import Prover.Prelude.Maybe
  using (Maybe; just; maybe; nothing)
open import Prover.Prelude.Nat
  using (Nat; ℕ; zero; suc)
open import Prover.Prelude.Sigma
  using (Σ; _,_)
open import Prover.Prelude.Sum
  using (_⊔_; ι₁; ι₂)

-- ## Definition

module _Fin where
  
  data Fin
    : ℕ
    → Set
    where
  
    zero
      : {n : ℕ}
      → Fin (suc n)
    suc
      : {n : ℕ}
      → Fin n
      → Fin (suc n)

Fin
  : ℕ
  → Set
Fin
  = _Fin.Fin

open _Fin.Fin public

-- ## Module

module Fin where

  open _Fin.Fin public

  -- ### Interface

  increment
    : {n : ℕ}
    → Fin n
    → Maybe (Fin n)
  increment {n = suc zero} zero
    = nothing
  increment {n = suc (suc n)} zero
    = just (suc zero)
  increment (suc k)
    = Maybe.map suc (increment k)

  decrement
    : {n : ℕ}
    → Fin n
    → Maybe (Fin n)
  decrement zero
    = nothing
  decrement (suc k)
    = just (maybe (decrement k) zero suc)

  increment-def
    : {n : ℕ}
    → Fin n 
    → Fin n
  increment-def k
    = maybe (increment k) k id

  decrement-def
    : {n : ℕ}
    → Fin n 
    → Fin n
  decrement-def k
    = maybe (decrement k) k id

  maximum
    : {n : ℕ}
    → Fin (suc n)
  maximum {n = zero}
    = zero
  maximum {n = suc n}
    = suc (maximum {n = n})

  drop
    : {n : ℕ}
    → Fin (suc n)
    → Maybe (Fin n)
  drop {n = zero} zero
    = nothing
  drop {n = suc _} zero
    = just zero
  drop {n = suc _} (suc k)
    = Maybe.map suc (drop k)

  -- ### Conversion

  to-nat
    : {n : ℕ}
    → Fin n
    → ℕ
  to-nat zero
    = zero
  to-nat (suc k)
    = suc (to-nat k)

  -- ### Equality

  _≟_fin
    : {n : ℕ}
    → Decidable (Fin n)
  
  zero ≟ zero fin
    = yes refl
  suc k₁ ≟ suc k₂ fin
    with k₁ ≟ k₂ fin
  ... | no ¬eq
    = no (λ {refl → ¬eq refl})
  ... | yes refl
    = yes refl
  
  zero ≟ suc _ fin
    = no (λ ())
  suc _ ≟ zero fin
    = no (λ ())

  -- ## Properties

  increment-maximum
    : {n : ℕ}
    → increment (maximum {n = n}) ≡ nothing
  increment-maximum {n = zero}
    = refl
  increment-maximum {n = suc n}
    with increment (maximum {n = n})
    | increment-maximum {n = n}
  ... | _ | refl
    = refl

  data IsSuc
    : {n : ℕ}
    → Fin n
    → Fin n
    → Set
    where

    zero
      : {n : ℕ}
      → IsSuc {n = suc (suc n)} zero (suc zero)

    suc
      : {n : ℕ}
      → {k₁ k₂ : Fin n}
      → IsSuc k₁ k₂
      → IsSuc (suc k₁) (suc k₂)

  is-suc
    : {n : ℕ}
    → (k : Fin (suc n))
    → k ≡ maximum ⊔ Σ (Fin (suc n)) (IsSuc k)
  is-suc {n = zero} zero
    = ι₁ refl
  is-suc {n = suc _} zero
    = ι₂ (suc zero , zero)
  is-suc {n = suc _} (suc k)
    with is-suc k
  ... | ι₁ refl
    = ι₁ refl
  ... | ι₂ (k' , p)
    = ι₂ (suc k' , suc p)

  is-suc-nonzero
    : {n : ℕ}
    → {k₁ k₂ : Fin (suc n)}
    → IsSuc k₁ k₂
    → k₂ ≢ zero
  is-suc-nonzero zero ()

  is-suc-to-nat
    : {n : ℕ}
    → {k₁ k₂ : Fin (suc n)}
    → IsSuc k₁ k₂
    → to-nat k₂ ≡ Nat.suc (to-nat k₁)
  is-suc-to-nat zero
    = refl
  is-suc-to-nat {n = suc _} (suc n)
    = sub suc (is-suc-to-nat n)

-- ## Exports

open Fin public
  using (_≟_fin)

