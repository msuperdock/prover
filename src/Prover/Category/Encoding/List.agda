module Prover.Category.Encoding.List where

open import Prover.Category.Encoding
  using (Encoding; encoding-from-split-function)
open import Prover.Function.Split.List
  using (split-function-list)
open import Prover.Prelude

-- ## Encoding

encoding-list
  : {A B : Set}
  → Encoding A B
  → Encoding (List A) (List B)
encoding-list e
  = encoding-from-split-function
  $ split-function-list
    (Encoding.split-function e)

