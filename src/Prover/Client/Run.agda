module Prover.Client.Run where

open import Prover.Client
  using (Client)
open import Prover.Client.Aeson
  using (Value; decode; encode; is-file; read-file; write-file)
open import Prover.Client.Brick
  using (App; AttributeMap; BrickEvent; CursorLocation; EventM; Next; Widget;
    app; attributes; continue; default-main; event-bind; event-pure;
    from-brick-event; halt; liftIO)
open import Prover.Client.Event
  using (SpecialEvent)
open import Prover.Client.Flat
  using (FlatClient)
open import Prover.Client.Flatten
  using (client-flatten)
open import Prover.Editor
  using (EventStack; MainEditor; ViewStack)
open import Prover.Editor.Flat
  using (FlatEventStack; FlatMainEditor; FlatViewStack)
open import Prover.Editor.Flatten
  using (main-editor-flatten)
open import Prover.Prelude

-- ## FlatMainEditor

module _
  {V : FlatViewStack}
  {E : FlatEventStack}
  where

  module FlatMainEditorRun
    (p : String)
    (e : FlatMainEditor V E Value)
    (c : FlatClient V E)
    where

    State
      : Set
    State
      = s ∈ FlatMainEditor.State e
      × FlatMainEditor.StatePath e s

    initial
      : Maybe Value
      → State
    initial nothing
      = FlatMainEditor.initial e
      , FlatMainEditor.initial-path e
    initial (just s)
      = FlatMainEditor.initial-with e s
      , FlatMainEditor.initial-path-with e s

    draw
      : State
      → List Widget
    draw (s , sp)
      = FlatClient.draw c
        (FlatMainEditor.draw-with e s sp)
        (FlatMainEditor.draw-path e s sp)
      ∷ []

    cursor
      : State
      → List CursorLocation
      → Maybe CursorLocation
    cursor _ []
      = nothing
    cursor _ (c ∷ _)
      = just c

    write
      : State
      → IO ⊤
    write (s , _)
      = write-file p (encode (FlatMainEditor.handle-save e s))

    handle
      : State
      → BrickEvent
      → EventM (Next State)
    handle (s , sp) e'
      with from-brick-event e'
    ... | nothing
      = continue (s , sp)
    ... | just e''
      with FlatClient.handle c (FlatMainEditor.mode e s sp) e''
    ... | nothing
      = continue (s , sp)
    ... | just (ι₁ e''')
      = continue (FlatMainEditor.handle e s sp e''')
    ... | just (ι₂ SpecialEvent.quit)
      = halt (s , sp)
    ... | just (ι₂ SpecialEvent.write)
      = event-bind (liftIO (write (s , sp))) (const (continue (s , sp)))
    ... | just (ι₂ SpecialEvent.escape)
      = continue (FlatMainEditor.handle-escape e s sp)
    ... | just (ι₂ SpecialEvent.return)
      = continue (FlatMainEditor.handle-return e s sp)
    ... | just (ι₂ (SpecialEvent.direction d))
      = continue (s , FlatMainEditor.handle-direction e s sp d)

    start
      : State
      → EventM State
    start
      = event-pure

    attributes'
      : State
      → AttributeMap
    attributes' _
      = attributes

    app'
      : App State
    app'
      = app draw cursor handle start attributes'

    decode-file
      : Bool
      → IO (Maybe Value)
    decode-file false
      = IO.return nothing
    decode-file true
      = read-file p
      >>= IO.return ∘ decode

    main
      : IO ⊤
    main
      = is-file p
      >>= decode-file
      >>= default-main app' ∘ initial
      >>= const (IO.return tt)

  flat-main-editor-run
    : String
    → FlatMainEditor V E Value
    → FlatClient V E
    → IO ⊤
  flat-main-editor-run
    = FlatMainEditorRun.main

-- ## MainEditor

main-editor-run
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → String
  → MainEditor V E Value A
  → Client V E
  → IO ⊤
main-editor-run p e c
  = flat-main-editor-run p
    (main-editor-flatten e)
    (client-flatten c)

