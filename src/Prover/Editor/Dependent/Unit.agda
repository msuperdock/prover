module Prover.Editor.Dependent.Unit where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Unit
  using (dependent-category-unit)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Dependent
  using (DependentEditor; DependentSimpleEditor; cons; dependent-simple-editor₀;
    dependent-simple-editor-tail; nil)
open import Prover.Editor.Unit
  using (editor-unit)
open import Prover.Prelude

-- ## DependentEditor

dependent-editor-unit
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleEditor V E C'
  → DependentEditor V E
    (dependent-category-unit C')
dependent-editor-unit
  {n = zero} e
  = nil
    (editor-unit
      (dependent-simple-editor₀ e))
dependent-editor-unit
  {n = suc _} e
  = cons
    (λ x → dependent-editor-unit
      (dependent-simple-editor-tail e x))

