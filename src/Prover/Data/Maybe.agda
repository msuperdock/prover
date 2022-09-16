module Prover.Data.Maybe where

open import Prover.Data.Equal
  using (_≢_)

import Data.Maybe
  as Maybe'

-- ## Definition

Maybe
  = Maybe'.Maybe

open Maybe' public
  using (just; nothing)

-- ## Module

module Maybe where

  open Maybe'.Maybe public

  nothing≢just
    : {A : Set}
    → {x : A}
    → nothing ≢ just x
  nothing≢just ()

-- ## Exports

open Maybe public
  using (maybe)

