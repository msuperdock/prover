module Prover.Encoding.Formula where

open import Client.Aeson
  using (Value)

open import Prover.Data.Any
  using (any)
open import Prover.Data.Bool
  using (Bool; true)
open import Prover.Data.Empty
  using (⊥-elim)
open import Prover.Data.Equal
  using (_≡_; refl)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Function
  using (_$_)
open import Prover.Data.Inspect
  using ([_]; inspect)
open import Prover.Data.List
  using (List; List')
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Nat
  using (ℕ; _≟_nat)
open import Prover.Data.Relation
  using (no; yes)
open import Prover.Data.Symbol
  using (Symbol; symbol)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Variable
  using (variable')
open import Prover.Data.Variables
  using (Variables)
open import Prover.Data.Vec
  using (Vec; []; _∷_)
open import Prover.Encoding.Text
  using (decode-encode-text; decode-text; encode-text)

open List'
  using () renaming
  ( nil
    to []'
  ; cons
    to _∷'_
  )

-- ## Pattern

pattern tag-meta
  = Value.string ('m' ∷' []')
pattern tag-variable
  = Value.string ('v' ∷' []')
pattern tag-symbol
  = Value.string ('s' ∷' []')

-- ## Encode

encode-formula
  : {ss : Symbols}
  → {vs : Variables}
  → {m : Bool}
  → Formula ss vs m
  → Value

encode-formulas
  : {ss : Symbols}
  → {vs : Variables}
  → {m : Bool}
  → {n : ℕ}
  → Vec (Formula ss vs m) n
  → List' Value

encode-formula (Formula.meta m)
  = Value.array
  $ tag-meta
  ∷' Value.number m
  ∷' []'

encode-formula (Formula.variable' (variable' n _) _)
  = Value.array 
  $ tag-variable
  ∷' encode-text n
  ∷' []'

encode-formula (Formula.symbol (symbol _ n _ _ _) _ fs)
  = Value.array
  $ tag-symbol
  ∷' encode-text n
  ∷' Value.array (encode-formulas fs)
  ∷' []'

encode-formulas []
  = []'
encode-formulas (f ∷ fs)
  = encode-formula f ∷' encode-formulas fs

-- ## Decode

decode-formula
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → Value
  → Maybe (Formula ss vs m)

decode-formulas
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → List' Value
  → Maybe (List (Formula ss vs m))

decode-formula _ vs _
  (Value.array (tag-variable ∷' n ∷' []'))
  with decode-text n
... | nothing
  = nothing
... | just n'
  with Variables.lookup-member vs n'
... | nothing
  = nothing
... | just (Variables.member v p)
  = just (Formula.variable' v p)

decode-formula ss vs m
  (Value.array (tag-symbol ∷' n ∷' Value.array fs ∷' []'))
  with decode-text n
  | decode-formulas ss vs m fs
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just n' | just (any {a} fs')
  with Symbols.lookup-member ss n'
... | nothing
  = nothing
... | just (Symbols.member s p)
  with Symbol.arity s ≟ a nat
... | no _
  = nothing
... | yes refl
  = just (Formula.symbol s p fs')

decode-formula _ _ true
  (Value.array (tag-meta ∷' Value.number n ∷' []'))
  = just (Formula.meta n)

decode-formula _ _ _ _
  = nothing

decode-formulas _ _ _ []'
  = just (any [])
decode-formulas ss vs m (f ∷' fs)
  with decode-formula ss vs m f
  | decode-formulas ss vs m fs
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just f' | just (any fs')
  = just (any (f' ∷ fs'))

-- ## Valid

decode-encode-formula
  : {ss : Symbols}
  → {vs : Variables}
  → {m : Bool}
  → (f : Formula ss vs m)
  → decode-formula ss vs m (encode-formula f) ≡ just f

decode-encode-formulas
  : {ss : Symbols}
  → {vs : Variables}
  → {m : Bool}
  → {n : ℕ}
  → (fs : Vec (Formula ss vs m) n)
  → decode-formulas ss vs m (encode-formulas fs) ≡ just (any fs)

decode-encode-formula
  (Formula.meta _)
  = refl

  -- As of 2.6.1.3, with-abstraction over `decode-encode-text` fails to match.
decode-encode-formula {vs = vs}
  (Formula.variable' v@(variable' n _) p)
  with List.from-builtin (List.to-builtin n)
  | List.from-to-builtin n
... | _ | refl
  with Variables.lookup-member vs n
  | inspect (Variables.lookup-member vs) n
... | nothing | [ q ]
  = ⊥-elim (Variables.lookup-member-nothing vs v q p)
... | just _ | [ q ]
  with Variables.lookup-member-just vs v p q
... | refl
  = refl

decode-encode-formula {ss = ss} {vs = vs} {m = m}
  (Formula.symbol s@(symbol _ n _ _ _) p fs)
  with decode-text (encode-text n)
  | decode-encode-text n
  | decode-formulas ss vs m (encode-formulas fs)
  | decode-encode-formulas fs
... | _ | refl | _ | refl
  with Symbols.lookup-member ss n
  | inspect (Symbols.lookup-member ss) n
... | nothing | [ q ]
  = ⊥-elim (Symbols.lookup-member-nothing ss s q p)
... | just _ | [ q ]
  with Symbols.lookup-member-just ss s p q
... | refl
  with Symbol.arity s ≟ Symbol.arity s nat
... | no ¬p
  = ⊥-elim (¬p refl)
... | yes refl
  = refl

decode-encode-formulas []
  = refl
decode-encode-formulas {ss = ss} {vs = vs} {m = m} (f ∷ fs)
  with decode-formula ss vs m (encode-formula f)
  | decode-encode-formula f
  | decode-formulas ss vs m (encode-formulas fs)
  | decode-encode-formulas fs
... | _ | refl | _ | refl
  = refl

