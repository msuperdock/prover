module Prover.Editor.Indexed.Unit where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSet)
open import Prover.Category.Indexed.Unit
  using (indexed-category-unit)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Indexed
  using (IndexedEditor; IndexedSimpleEditor; empty; indexed-simple-editor₀;
    indexed-simple-editor-tail; sigma)
open import Prover.Editor.Unit
  using (editor-unit)
open import Prover.Prelude

-- ## IndexedEditor

indexed-editor-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedSet C}
  → IndexedSimpleEditor V E C'
  → IndexedEditor V E
    (indexed-category-unit C')
indexed-editor-unit {n = zero} e
  = empty (editor-unit (indexed-simple-editor₀ e))
indexed-editor-unit {n = suc _} e
  = sigma (λ x → indexed-editor-unit (indexed-simple-editor-tail e x))

