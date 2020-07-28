module Prover.Prelude.Digit where

open import Prover.Prelude.Any
  using (any)
open import Prover.Prelude.Empty
  using (⊥-elim)
open import Prover.Prelude.Equal
  using (_≡_; _≢_; refl; sub; trans)
open import Prover.Prelude.Fin
  using (Fin; _≟_fin; suc; zero)
open import Prover.Prelude.Function
  using (_$_)
open import Prover.Prelude.Inspect
  using ([_]; inspect)
open import Prover.Prelude.List
  using (List)
open import Prover.Prelude.List1
  using (List₁)
open import Prover.Prelude.Nat
  using (ℕ; _+_; _*_; suc; zero)
open import Prover.Prelude.Relation
  using (no; yes)
open import Prover.Prelude.Retraction
  using (Retraction; retraction-compose)
open import Prover.Prelude.Sigma
  using (_,_)
open import Prover.Prelude.Sum
  using (ι₁; ι₂)
open import Prover.Prelude.Vec
  using (cons)

open List
  using ([]; _∷_)

-- ## Internal

module Internal where

  -- ### Definitions

  Digit
    : Set
  Digit
    = Fin 10

  pattern 0d
    = zero
  pattern 1d
    = suc zero
  pattern 2d
    = suc (suc zero)
  pattern 3d
    = suc (suc (suc zero))
  pattern 4d
    = suc (suc (suc (suc zero)))
  pattern 5d
    = suc (suc (suc (suc (suc zero))))
  pattern 6d
    = suc (suc (suc (suc (suc (suc zero)))))
  pattern 7d
    = suc (suc (suc (suc (suc (suc (suc zero))))))
  pattern 8d
    = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  pattern 9d
    = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

  Digits
    : Set
  Digits
    = List₁ Digit

  data Digits₁
    : Set
    where

    digits₁
      : (ds : List Digit)
      → .(ds ≢ [])
      → Digits₁

  data Digits₂
    : Set
    where

    digits₂
      : (ds : List Digit)
      → .(ds ≢ 0d ∷ [])
      → Digits₂

  -- ### Interface

  data DigitsIsSuc
    : List Digit
    → List Digit
    → Set
    where

    nil
      : DigitsIsSuc [] (1d ∷ [])

    head
      : {d₁ d₂ : Digit}
      → {ds : List Digit}
      → Fin.IsSuc d₁ d₂
      → DigitsIsSuc (d₁ ∷ ds) (d₂ ∷ ds)

    tail
      : {ds₁ ds₂ : List Digit}
      → DigitsIsSuc ds₁ ds₂
      → DigitsIsSuc (9d ∷ ds₁) (0d ∷ ds₂)
      
  digits-is-suc-nonzero₀
    : {ds₁ ds₂ : List Digit}
    → DigitsIsSuc ds₁ ds₂
    → ds₂ ≢ []
  digits-is-suc-nonzero₀ nil ()

  digits-is-suc-nonzero
    : {ds₁ ds₂ : List Digit}
    → DigitsIsSuc ds₁ ds₂
    → ds₂ ≢ 0d ∷ []
  digits-is-suc-nonzero (head p) refl
    = Fin.is-suc-nonzero p refl
  digits-is-suc-nonzero (tail p) refl
    = digits-is-suc-nonzero₀ p refl

  data DigitsIsSucResult
    (ds : List Digit)
    : Set
    where

    digits-is-suc-result
      : (ds' : List Digit)
      → DigitsIsSuc ds ds'
      → DigitsIsSucResult ds

  digits-is-suc
    : (ds : List Digit)
    → DigitsIsSucResult ds
  digits-is-suc []
    = digits-is-suc-result (1d ∷ []) nil
  digits-is-suc (d ∷ ds)
    with Fin.is-suc d
    | digits-is-suc ds
  ... | ι₁ refl | digits-is-suc-result ds' p
    = digits-is-suc-result (0d ∷ ds') (tail p)
  ... | ι₂ (d' , p) | _
    = digits-is-suc-result (d' ∷ ds) (head p)

  -- ### Conversion

  digits-from-nat
    : ℕ
    → Digits₂
  digits-from-nat zero
    = digits₂ [] (λ ())
  digits-from-nat (suc n)
    with digits-from-nat n
  ... | digits₂ ds _
    with digits-is-suc ds
  ... | digits-is-suc-result ds' p
    = digits₂ ds' (digits-is-suc-nonzero p)

  digits-to-nat
    : List Digit
    → ℕ
  digits-to-nat []
    = zero
  digits-to-nat (d ∷ ds)
    = Fin.to-nat d + digits-to-nat ds * 10

  digits-is-suc-to-nat
    : {ds₁ ds₂ : List Digit}
    → DigitsIsSuc ds₁ ds₂
    → digits-to-nat ds₂ ≡ suc (digits-to-nat ds₁)
  digits-is-suc-to-nat nil
    = refl
  digits-is-suc-to-nat (head {d₂ = d₂} p)
    with Fin.to-nat d₂
    | Fin.is-suc-to-nat p
  ... | _ | refl
    = refl
  digits-is-suc-to-nat {ds₁ = _ ∷ ds₁} {ds₂ = _ ∷ ds₂} (tail p)
    with digits-to-nat ds₂
    | digits-is-suc-to-nat p
  ... | _ | refl
    = refl

  -- ### Retractions

  module DigitsRetraction₁ where

    to
      : Digits
      → Digits₁
    to (any ds)
      = digits₁ (any ds) (λ ())

    from
      : Digits₁
      → Digits
    from (digits₁ [] ¬p)
      = ⊥-elim (¬p refl)
    from (digits₁ (d ∷ ds) _)
      = any (cons d ds)

    to-from
      : (ds : Digits₁)
      → to (from ds) ≡ ds
    to-from (digits₁ [] ¬p)
      = ⊥-elim (¬p refl)
    to-from (digits₁ (_ ∷ _) _)
      = refl

  digits-retraction₁
    : Retraction Digits Digits₁
  digits-retraction₁
    = record {DigitsRetraction₁}

  module DigitsRetraction₂ where

    to
      : Digits₁
      → Digits₂
    to (digits₁ ds _)
      with List.decidable _≟_fin ds (0d ∷ [])
    ... | no ¬p
      = digits₂ ds ¬p
    ... | yes _
      = digits₂ [] (λ ())

    from
      : Digits₂
      → Digits₁
    from (digits₂ ds _)
      with List.decidable _≟_fin ds []
    ... | no ¬p
      = digits₁ ds ¬p
    ... | yes _
      = digits₁ (0d ∷ []) (λ ())

    to-from
      : (ds : Digits₂)
      → to (from ds) ≡ ds
    to-from (digits₂ ds ¬p)
      with List.decidable _≟_fin ds []
    ... | yes refl
      = refl
    ... | no _
      with List.decidable _≟_fin ds (0d ∷ [])
    ... | no _
      = refl
    ... | yes refl
      = ⊥-elim (¬p refl)

  digits-retraction₂
    : Retraction Digits₁ Digits₂
  digits-retraction₂
    = record {DigitsRetraction₂}

  module DigitsRetraction₃ where

    to
      : Digits₂
      → ℕ
    to (digits₂ ds _)
      = digits-to-nat ds

    from
      : ℕ
      → Digits₂
    from
      = digits-from-nat

    to-from
      : (n : ℕ)
      → to (from n) ≡ n
    to-from zero
      = refl
    to-from (suc n)
      with digits-from-nat n
      | inspect digits-from-nat n
    ... | digits₂ ds _ | [ p ]
      with digits-is-suc ds
      | to-from n
    ... | digits-is-suc-result _ q | r
      with digits-from-nat n
      | p
    ... | _ | refl
      = trans (digits-is-suc-to-nat q) (sub suc r)

  digits-retraction₃
    : Retraction Digits₂ ℕ
  digits-retraction₃
    = record {DigitsRetraction₃}

  digits-retraction
    : Retraction Digits ℕ
  digits-retraction
    = retraction-compose digits-retraction₃
    $ retraction-compose digits-retraction₂
    $ digits-retraction₁

-- ## Modules

-- ### Digit

Digit
  : Set
Digit
  = Internal.Digit

open Internal public
  using (0d; 1d; 2d; 3d; 4d; 5d; 6d; 7d; 8d; 9d)

-- ### Digits

module Digits where

  open Internal public using () renaming
    ( digits-retraction
      to retraction
    )

