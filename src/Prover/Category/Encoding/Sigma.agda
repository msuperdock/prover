module Prover.Category.Encoding.Sigma where

open import Prover.Category.Encoding
  using (Encoding)
open import Prover.Prelude

-- ## Encoding

module _
  {A₁ B₁ B₂ : Set}
  (A₂ : A₁ → Set)
  where

  module EncodingSigma
    (e₁ : Encoding A₁ B₁)
    (e₂ : ((x₁ : A₁) → Encoding (A₂ x₁) B₂))
    where

    encode
      : Σ A₁ A₂
      → B₁ × B₂
    encode (x₁ , x₂)
      = Encoding.encode e₁ x₁
      , Encoding.encode (e₂ x₁) x₂
    
    decode
      : B₁ × B₂
      → Maybe (Σ A₁ A₂)
    decode (x₁' , x₂')
      with Encoding.decode e₁ x₁'
    ... | nothing
      = nothing
    ... | just x₁
      with Encoding.decode (e₂ x₁) x₂'
    ... | nothing
      = nothing
    ... | just x₂
      = just (x₁ , x₂)

    decode-encode
      : (x : Σ A₁ A₂)
      → decode (encode x) ≡ just x
    decode-encode (x₁ , x₂)
      with Encoding.decode e₁ (Encoding.encode e₁ x₁)
      | Encoding.decode-encode e₁ x₁
    ... | _ | refl
      with Encoding.decode (e₂ x₁) (Encoding.encode (e₂ x₁) x₂)
      | Encoding.decode-encode (e₂ x₁) x₂
    ... | _ | refl
      = refl

  encoding-sigma
    : Encoding A₁ B₁
    → ((x₁ : A₁) → Encoding (A₂ x₁) B₂)
    → Encoding (Σ A₁ A₂) (B₁ × B₂)
  encoding-sigma e₁ e₂
    = record {EncodingSigma e₁ e₂}

