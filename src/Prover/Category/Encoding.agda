module Prover.Category.Encoding where

open import Prover.Function
  using (Function)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Function.Split.Compose
  using (split-function-compose)
open import Prover.Prelude

-- ## Definition

record Encoding
  (A B : Set)
  : Set
  where

  field

    encode
      : A
      → B
    
  function
    : Function A B
  function
    = record
    { base
      = encode
    }

  field

    decode
      : B
      → Maybe A

  partial-function
    : PartialFunction B A
  partial-function
    = record
    { base
      = decode
    }

  field

    decode-encode
      : (x : A)
      → decode (encode x) ≡ just x

  split-function
    : SplitFunction B A
  split-function
    = record
    { partial-function
      = partial-function
    ; function
      = function
    ; base-unbase
      = decode-encode
    }

-- ## Conversion

split-function-encoding
  : {A B : Set}
  → SplitFunction A B
  → Encoding B A
split-function-encoding F
  = record
  { encode
    = SplitFunction.unbase F
  ; decode
    = SplitFunction.base F
  ; decode-encode
    = SplitFunction.base-unbase F
  }

-- ## Map

encoding-map
  : {A B C : Set}
  → SplitFunction A C
  → Encoding A B
  → Encoding C B
encoding-map F e
  = split-function-encoding
  $ split-function-compose F
    (Encoding.split-function e)

encoding-comap
  : {A B C : Set}
  → SplitFunction C B
  → Encoding A B
  → Encoding A C
encoding-comap F e
  = split-function-encoding
  $ split-function-compose
    (Encoding.split-function e) F

