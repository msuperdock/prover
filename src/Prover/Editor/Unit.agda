module Prover.Editor.Unit where

open import Prover.Category
  using (Category)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Category.Split.Unit
  using (split-functor-unit)
open import Prover.Category.Unit
  using (module CategoryUnit; category-unit)
open import Prover.Editor
  using (Editor; EventStack; SimpleEditor; SplitEditor; ViewStack;
    simple-editor)
open import Prover.Prelude

-- ## Editor

module _
  {V : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  module EditorUnit
    {C : Category}
    (e : Editor V E C)
    where

    open EventStack E

    open Category (category-unit (Category.Object C)) using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      ; identity
        to state-identity
      ; compose
        to state-compose
      ; precompose
        to state-precompose
      ; postcompose
        to state-postcompose
      ; associative
        to state-associative
      )

    open Editor e public
      hiding (handle; handle-escape; handle-return; handle-inner-return)

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle s sp e'
      with Editor.handle e s sp e'
    ... | ι₁ (s' , sp' , _)
      = ι₁ (s' , sp' , CategoryUnit.arrow)
    ... | ι₂ s'
      = ι₂ s'

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape s sp
      with Editor.handle-escape e s sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , _))
      = just (ι₁ (s' , sp' , CategoryUnit.arrow))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return s sp
      with Editor.handle-return e s sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , _))
      = just (ι₁ (s' , sp' , CategoryUnit.arrow))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return s sp s' sp'
      with Editor.handle-inner-return e s sp s' sp'
    ... | ι₁ (s'' , sp'' , _)
      = ι₁ (s'' , sp'' , CategoryUnit.arrow)
    ... | ι₂ s''
      = ι₂ s''

  editor-unit
    : SimpleEditor V E A
    → Editor V E (category-unit A)
  editor-unit (simple-editor e)
    = record {EditorUnit e}

-- ## SplitEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {A B : Set}
  where

  module SplitEditorUnit
    (F : PartialRetraction A B)
    (e : SimpleEditor V E A)
    where

    StateCategory
      : Category
    StateCategory
      = category-unit A

    editor
      : Editor V E StateCategory
    editor
      = editor-unit e

    split-functor
      : SplitFunctor StateCategory (category-unit B)
    split-functor
      = split-functor-unit F

  split-editor-unit
    : PartialRetraction A B
    → SimpleEditor V E A
    → SplitEditor V E (category-unit B)
  split-editor-unit F e
    = record {SplitEditorUnit F e}

