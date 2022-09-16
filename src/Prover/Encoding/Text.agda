module Prover.Encoding.Text where

open import Client.Aeson
  using (Value)

open import Prover.Data.Equal
  using (_≡_; sub)
open import Prover.Data.List
  using (List)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Text
  using (Text)

-- ## Encode

encode-text
  : Text
  → Value
encode-text cs
  = Value.string (List.to-builtin cs)

-- ## Decode

decode-text
  : Value
  → Maybe Text
decode-text (Value.string cs)
  = just (List.from-builtin cs)
decode-text _
  = nothing

-- ## Valid

decode-encode-text
  : (t : Text)
  → decode-text (encode-text t) ≡ just t
decode-encode-text cs
  = sub just (List.from-to-builtin cs)

