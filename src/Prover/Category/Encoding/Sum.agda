module Prover.Category.Encoding.Sum where

open import Prover.Category.Encoding
  using (Encoding)
open import Prover.Prelude

-- ## Encoding

module _
  {A₁ A₂ B₁ B₂ : Set}
  where

  module EncodingSum
    (e₁ : Encoding A₁ B₁)
    (e₂ : Encoding A₂ B₂)
    where

    encode
      : A₁ ⊔ A₂
      → B₁ ⊔ B₂
    encode (ι₁ x₁)
      = ι₁ (Encoding.encode e₁ x₁)
    encode (ι₂ x₂)
      = ι₂ (Encoding.encode e₂ x₂)
    
    decode
      : B₁ ⊔ B₂
      → Maybe (A₁ ⊔ A₂)
    decode (ι₁ x₁')
      = Maybe.map ι₁ (Encoding.decode e₁ x₁')
    decode (ι₂ x₂')
      = Maybe.map ι₂ (Encoding.decode e₂ x₂')

    decode-encode
      : (x : A₁ ⊔ A₂)
      → decode (encode x) ≡ just x
    decode-encode (ι₁ x₁)
      = sub (Maybe.map ι₁) (Encoding.decode-encode e₁ x₁)
    decode-encode (ι₂ x₂)
      = sub (Maybe.map ι₂) (Encoding.decode-encode e₂ x₂)

  encoding-sum
    : Encoding A₁ B₁
    → Encoding A₂ B₂
    → Encoding (A₁ ⊔ A₂) (B₁ ⊔ B₂)
  encoding-sum e₁ e₂
    = record {EncodingSum e₁ e₂}

