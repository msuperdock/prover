module Prover.Client.Run where

open import Prover.Category
  using (Category)
open import Prover.Client
  using (Client)
open import Prover.Client.Brick
  using (App; AttributeMap; BrickEvent; CursorLocation; EventM; Next; Widget;
    app; attributes; continue; default-main; from-brick-event; halt; pure)
open import Prover.Client.Event
  using (SpecialEvent)
open import Prover.Client.Flat
  using (FlatClient)
open import Prover.Client.Flatten
  using (client-flatten)
open import Prover.Editor
  using (Editor; EventStack; PartialEditor; SimpleEditor; SplitEditor;
    ViewStack; any)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatViewStack)
open import Prover.Editor.Flatten
  using (editor-flatten)
open import Prover.Prelude

-- ## FlatEditor

module _
  {V : FlatViewStack}
  {E : FlatEventStack}
  {A : Set}
  where

  module FlatEditorRun
    (e : FlatEditor V E A)
    (c : FlatClient V E)
    where

    State
      : Set
    State
      = Σ (FlatEditor.State e) (FlatEditor.StatePath e)

    initial
      : State
    initial
      = (FlatEditor.initial e , FlatEditor.initial-path e)

    draw
      : State
      → List Widget
    draw (s , sp)
      = FlatClient.draw c
        (FlatEditor.draw-with e s sp)
        (FlatEditor.draw-path e s sp)
      ∷ []

    cursor
      : State
      → List CursorLocation
      → Maybe CursorLocation
    cursor _ []
      = nothing
    cursor _ (c ∷ _)
      = just c

    handle
      : State
      → BrickEvent
      → EventM (Next State)
    handle (s , sp) e'
      with from-brick-event e'
    ... | nothing
      = continue (s , sp)
    ... | just e''
      with FlatClient.handle c (FlatEditor.mode e s sp) e''
    ... | nothing
      = continue (s , sp)
    ... | just (ι₁ e''')
      = continue (FlatEditor.handle e s sp e''')
    ... | just (ι₂ SpecialEvent.escape)
      = maybe (FlatEditor.handle-escape e s sp)
        (halt (s , sp)) continue
    ... | just (ι₂ SpecialEvent.return)
      = sum (FlatEditor.handle-return e s sp)
        (const (continue (s , sp))) continue
    ... | just (ι₂ (SpecialEvent.direction d))
      = continue (s , FlatEditor.handle-direction e s sp d)

    start
      : State
      → EventM State
    start
      = pure

    attributes'
      : State
      → AttributeMap
    attributes' _
      = attributes

    app'
      : App State
    app'
      = app draw cursor handle start attributes'

    main
      : IO ⊤
    main
      = IO.void (default-main app' initial)

  flat-editor-run
    : FlatEditor V E A
    → FlatClient V E
    → IO ⊤
  flat-editor-run
    = FlatEditorRun.main

-- ## Editor

editor-run
  : {V : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → Editor V E C
  → Client V E
  → IO ⊤
editor-run e c
  = flat-editor-run
    (editor-flatten e)
    (client-flatten c)

-- ## SimpleEditor

simple-editor-run
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → SimpleEditor V E A
  → Client V E
  → IO ⊤
simple-editor-run (any e)
  = editor-run e

-- ## PartialEditor

partial-editor-run
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → PartialEditor V E A
  → Client V E
  → IO ⊤
partial-editor-run e c
  = simple-editor-run (PartialEditor.simple-editor e) c

-- ## SplitEditor

split-editor-run
  : {V : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → SplitEditor V E C
  → Client V E
  → IO ⊤
split-editor-run e c
  = editor-run (SplitEditor.editor e) c

