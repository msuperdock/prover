module Prover.Encoding.Proof where

open import Client.Aeson
  using (Value)
open import Encoding
  using (Encoding)

open import Prover.Data.Any
  using (any)
open import Prover.Data.Bool
  using (true)
open import Prover.Data.Empty
  using (⊥-elim)
open import Prover.Data.Equal
  using (_≡_; refl)
open import Prover.Data.Formula
  using (Formula; _≟_frm)
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
open import Prover.Data.Proof
  using (Branch; Proof; proof)
open import Prover.Data.Relation
  using (no; yes)
open import Prover.Data.Rule
  using (Rule; rule)
open import Prover.Data.Rules
  using (Rules)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Data.Vec
  using (Vec; []; _∷_)
open import Prover.Encoding.Formula
  using (decode-encode-formula; decode-formula; encode-formula)
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

pattern tag-assumption
  = Value.string ('a' ∷' []')
pattern tag-rule
  = Value.string ('r' ∷' []')

-- ## Encode

encode-branch
  : {ss : Symbols}
  → {rs : Rules ss}
  → {vs : Variables}
  → Branch rs vs
  → Value

encode-branches
  : {ss : Symbols}
  → {rs : Rules ss}
  → {vs : Variables}
  → {n : ℕ}
  → Vec (Branch rs vs) n
  → List' Value

encode-branch (Branch.assumption c)
  = Value.array
  $ tag-assumption
  ∷' encode-formula c
  ∷' []'

encode-branch (Branch.rule (rule n _ _ _) _ bs c _)
  = Value.array
  $ tag-rule
  ∷' encode-text n
  ∷' Value.array (encode-branches bs)
  ∷' encode-formula c
  ∷' []'

encode-branches []
  = []'
encode-branches (b ∷ bs)
  = encode-branch b ∷' encode-branches bs

encode-proof
  : {ss : Symbols}
  → {rs : Rules ss}
  → {r : Rule ss}
  → Proof rs r
  → Value
encode-proof (proof b _)
  = encode-branch b

-- ## Decode

decode-branch
  : {ss : Symbols}
  → (rs : Rules ss)
  → (vs : Variables)
  → Value
  → Maybe (Branch rs vs)

decode-branches
  : {ss : Symbols}
  → (rs : Rules ss)
  → (vs : Variables)
  → List' Value
  → Maybe (List (Branch rs vs))

decode-branch {ss = ss} _ vs
  (Value.array (tag-assumption ∷' c ∷' []'))
  = Maybe.map Branch.assumption (decode-formula ss vs true c)

decode-branch {ss = ss} rs vs
  (Value.array (tag-rule ∷' n ∷' Value.array bs ∷' c ∷' []'))
  with decode-text n
  | decode-branches rs vs bs
  | decode-formula ss vs true c
... | nothing | _ | _
  = nothing
... | _ | nothing | _
  = nothing
... | _ | _ | nothing
  = nothing
... | just n' | just (any {a} bs') | just c'
  with Rules.lookup-member rs n'
... | nothing
  = nothing
... | just (Rules.member r p)
  with Rule.arity r ≟ a nat
... | no _
  = nothing
... | yes refl
  with Rule.match? r (Vec.map Branch.conclusion bs') c'
... | no _
  = nothing
... | yes m
  = just (Branch.rule r p bs' c' m)

decode-branch _ _ _
  = nothing

decode-branches _ _ []'
  = just (any [])
decode-branches rs vs (p ∷' ps)
  with decode-branch rs vs p
  | decode-branches rs vs ps
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just b | just (any bs)
  = just (any (b ∷ bs))

decode-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → Value
  → Maybe (Proof rs r)
decode-proof rs (rule _ vs _ c) v
  with decode-branch rs vs v
... | nothing
  = nothing
... | just b
  with Branch.conclusion b ≟ (Formula.to-meta-formula c) frm
... | no _
  = nothing
... | yes q
  = just (proof b q)

-- ## Valid

decode-encode-branch
  : {ss : Symbols}
  → {rs : Rules ss}
  → {vs : Variables}
  → (b : Branch rs vs)
  → decode-branch rs vs (encode-branch b) ≡ just b

decode-encode-branches
  : {ss : Symbols}
  → {rs : Rules ss}
  → {vs : Variables}
  → {n : ℕ}
  → (bs : Vec (Branch rs vs) n)
  → decode-branches rs vs (encode-branches bs) ≡ just (any bs)

decode-encode-branch {ss = ss} {vs = vs}
  (Branch.assumption c)
  with decode-formula ss vs true (encode-formula c)
  | decode-encode-formula c
... | _ | refl
  = refl

decode-encode-branch {ss = ss} {rs = rs} {vs = vs}
  (Branch.rule r@(rule n _ _ _) p bs c m)
  with decode-text (encode-text n)
  | decode-encode-text n
  | decode-branches rs vs (encode-branches bs)
  | decode-encode-branches bs
  | decode-formula ss vs true (encode-formula c)
  | decode-encode-formula c
... | _ | refl | _ | refl | _ | refl
  with Rules.lookup-member rs n
  | inspect (Rules.lookup-member rs) n
... | nothing | [ q ] 
  = ⊥-elim (Rules.lookup-member-nothing rs r q p)
... | just _ | [ q ]
  with Rules.lookup-member-just rs r p q
... | refl
  with Rule.arity r ≟ Rule.arity r nat
... | no ¬p
  = ⊥-elim (¬p refl)
... | yes refl
  with Rule.match? r (Vec.map Branch.conclusion bs) c
... | no ¬m
  = ⊥-elim (¬m m)
... | yes _
  = refl

decode-encode-branches []
  = refl
decode-encode-branches {rs = rs} {vs = vs} (b ∷ bs)
  with decode-branch rs vs (encode-branch b)
  | decode-encode-branch b
  | decode-branches rs vs (encode-branches bs)
  | decode-encode-branches bs
... | _ | refl | _ | refl
  = refl

decode-encode-proof
  : {ss : Symbols}
  → {rs : Rules ss}
  → {r : Rule ss}
  → (p : Proof rs r)
  → decode-proof rs r (encode-proof p) ≡ just p
decode-encode-proof {rs = rs} {r = r} (proof b q)
  with decode-branch rs (Rule.variables r) (encode-branch b)
  | decode-encode-branch b
... | _ | refl
  with Branch.conclusion b ≟ (Formula.to-meta-formula (Rule.conclusion r)) frm
... | no ¬q
  = ⊥-elim (¬q q)
... | yes _
  = refl

-- ## Record

encoding-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → Encoding (Proof rs r) Value
encoding-proof rs r
  = record
  { encode
    = encode-proof
  ; decode
    = decode-proof rs r
  ; decode-encode
    = decode-encode-proof
  }

