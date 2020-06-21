module Prover.Prelude where

open import Prover.Prelude.Any public
  using (Any; any)
open import Prover.Prelude.Any1 public
  using (Any₁)
open import Prover.Prelude.Bool public
  using (Bool; T; _∨_; _∧_; _≟_bool; bool; false; not; true)
open import Prover.Prelude.Char public
  using (Char; _≟_char)
open import Prover.Prelude.CharWith public
  using (CharWith; char-with)
open import Prover.Prelude.Collection public
  using (Collection)
open import Prover.Prelude.Decidable public
  using (Dec; Decidable; no; recompute; yes)
open import Prover.Prelude.Direction public
  using (Direction; _≟_dir)
open import Prover.Prelude.Empty public
  using (¬_; ⊥; ⊥-elim)
open import Prover.Prelude.Equality public
  using (Equal; _≅_; _≡_; _≢_; irrelevant; rewrite'; refl; sub; sym; trans)
open import Prover.Prelude.Fin public
  using (Fin; _≟_fin; zero; suc)
open import Prover.Prelude.FinSet public
  using (FinSet)
open import Prover.Prelude.Function public
  using (_$_; _∘_; const; id)
open import Prover.Prelude.If public
  using (If; just; nothing)
open import Prover.Prelude.Inspect public
  using (Inspect; [_]; inspect)
open import Prover.Prelude.IO public
  using (IO; _>>=_)
open import Prover.Prelude.Level public
  using (Level; lmax)
open import Prover.Prelude.List public
  using (List; []; _∷_)
open import Prover.Prelude.Map public
  using (Map)
open import Prover.Prelude.Maybe public
  using (Maybe; just; maybe; nothing)
open import Prover.Prelude.Nat public
  using (Nat; ℕ; _+_; _*_; _≟_nat; _<_nat; s<s; z<s; zero; suc)
open import Prover.Prelude.Pair public
  using (Pair; pair)
open import Prover.Prelude.Retraction public
  using (Retraction; retraction-compose; retraction-identity)
open import Prover.Prelude.Sigma public
  using (Sigma; Σ; _,_; _×_; π₁; π₂)
open import Prover.Prelude.String public
  using (String)
open import Prover.Prelude.Sum public
  using (Sum; _⊔_; ι₁; ι₂; sum)
open import Prover.Prelude.Trichotomous public
  using (Tri; Trichotomous; equal; greater; less)
open import Prover.Prelude.Unit public
  using (⊤; tt)
open import Prover.Prelude.Vec public
  using (Vec; []; _∷_; _!_)

