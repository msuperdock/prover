module Prover.Data.Identifier.Editor where

open import Prover.Data.Text.Editor public using () renaming
  ( decode-encode-text
    to decode-encode-identifier
  ; decode-text
    to decode-identifier
  ; encode-text
    to encode-identifier
  )

