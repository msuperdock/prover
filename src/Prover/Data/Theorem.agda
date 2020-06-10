module Prover.Data.Theorem where

open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Proof
  using (Proof)
open import Prover.Data.Rule
  using (Rule)
open import Prover.Data.Rule.Collection
  using (Rules)
open import Prover.Data.Symbol.Collection
  using (Symbols)
open import Prover.Prelude

record Theorem
  {ss : Symbols}
  (rs : Rules ss)
  : Set
  where
  
  constructor
  
    theorem

  field

    {arity}
      : ℕ

    rule
      : Rule ss arity

    proof
      : Proof rs (Rule.variables rule)

    valid
      : Proof.conclusion proof ≡ Formula.to-meta-formula (Rule.conclusion rule)

