module Prover.Prelude.IO where

open import Prover.Prelude.Function
  using (const)
open import Prover.Prelude.Unit
  using (⊤; tt)

open import Agda.Builtin.IO public
  using (IO)

module IO where

  postulate

    return
      : {A : Set}
      → A
      → IO A

    _>>=_ 
      : {A B : Set}
      → IO A
      → (A → IO B)
      → IO B

  {-# COMPILE GHC return
    = \_ -> return #-}
  {-# COMPILE GHC _>>=_
    = \_ _ -> (>>=) #-}

  void
    : {A : Set}
    → IO A
    → IO ⊤
  void x
    = x >>= const (return tt)
  
open IO public
  using (_>>=_)

