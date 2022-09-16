module Main where

open import Client
  using (Client)
open import Client.Aeson
  using (Value)
open import Client.Brick
  using (Attribute; AttributeName; InputEvent; Widget)
open import Client.Event
  using (SpecialEvent)
open import Client.Run
  using (simple-main-editor-run)
open import Editor.Simple
  using (SimpleMainEditor)
open import Editor.Simple.Map.View
  using (simple-main-editor-map-view-with)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)
open import Event.Text
  using (TextEvent)
open import Event.TextWith
  using (TextWithEvent)

open import Examples
  using (∧-commutative; rules)
open import Prover.Client
  using (attributes'; draw-interface-with)
open import Prover.Data.Bool
  using (Bool)
open import Prover.Data.Char
  using (Char)
open import Prover.Data.CharWith
  using (char-with)
open import Prover.Data.Direction
  using (Direction)
open import Prover.Data.Fin
  using (suc; zero)
open import Prover.Data.Function
  using (_$_; id)
open import Prover.Data.IO
  using (IO)
open import Prover.Data.List
  using (List; []; _∷_)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Relation
  using (no; yes)
open import Prover.Data.Rule
  using (Rule)
open import Prover.Data.Rules
  using (Rules)
open import Prover.Data.Sigma
  using (_×_)
open import Prover.Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Unit
  using (⊤)
open import Prover.Editor.Simple.Proof
  using (simple-main-editor-proof)
open import Prover.Event.Formula
  using (FormulaEvent)
open import Prover.Event.Proof
  using (ProofEvent; ProofModeInner)
open import Prover.Stack.Proof
  using (event-stack-proof; view-stack-proof)
open import Prover.View.Interface
  using (command; interface; nothing; window)
open import Prover.View.Proof
  using (ProofViewInner; ProofViewInnerPath; both; command; window)
open import Prover.View.Window
  using (Window)

-- ## Types

view-stack-proof-window
  : ViewStack
view-stack-proof-window
  = record
  { View
    = Window
  ; ViewPath
    = λ _ → ⊤
  ; ViewInner
    = λ _ _ → ProofViewInner
  ; ViewInnerPath
    = λ _ _ → ProofViewInnerPath
  }

-- ## Editor

module ViewStackMapProof
  (b : Bool)
  where

  view
    : ViewStack.View view-stack-proof
    → ViewStack.View view-stack-proof-window
  view ls
    = record
    { name
      = "proof"
    ; status
      = b
    ; lines
      = ls
    }

  view-with
    : (v : ViewStack.View view-stack-proof)
    → ViewStack.ViewPath view-stack-proof v
    → ViewStack.View view-stack-proof-window
  view-with v _
    = view v
  
  view-path
    : (v : ViewStack.View view-stack-proof)
    → (vp : ViewStack.ViewPath view-stack-proof v)
    → ViewStack.ViewPath view-stack-proof-window
      (view-with v vp)
  view-path _
    = id

  view-inner-with
    : (v : ViewStack.View view-stack-proof)
    → (vp : ViewStack.ViewPath view-stack-proof v)
    → (v' : ViewStack.ViewInner view-stack-proof v vp)
    → ViewStack.ViewInnerPath view-stack-proof v vp v'
    → ViewStack.ViewInner view-stack-proof-window
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ _ v _
    = v

  view-inner-path
    : (v : ViewStack.View view-stack-proof)
    → (vp : ViewStack.ViewPath view-stack-proof v)
    → (v' : ViewStack.ViewInner view-stack-proof v vp)
    → (vp' : ViewStack.ViewInnerPath view-stack-proof v vp v')
    → ViewStack.ViewInnerPath view-stack-proof-window
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ _ _
    = id

view-stack-map-proof
  : Bool
  → ViewStackMap
    view-stack-proof
    view-stack-proof-window
view-stack-map-proof b
  = record {ViewStackMapProof b}

simple-main-editor-proof-window
  : {ss : Symbols}
  → Rules ss
  → Rule ss
  → SimpleMainEditor
    view-stack-proof-window
    event-stack-proof
    Value
simple-main-editor-proof-window rs r
  = simple-main-editor-map-view-with view-stack-map-proof
  $ simple-main-editor-proof rs r

-- ## Client

module ClientProof where

  open ViewStack view-stack-proof-window
  open EventStack event-stack-proof

  attributes
    : List (AttributeName × Attribute)
  attributes
    = attributes'

  draw
    : (v : View)
    → ViewPath v
    → Widget
  draw w _
    = draw-interface-with
      (interface nothing (w ∷ []))
      nothing

  draw-inner
    : (v : View)
    → (vp : ViewPath v)
    → (v' : ViewInner v vp)
    → ViewInnerPath v vp v'
    → Widget
  draw-inner w _ (window w') (window wp)
    = draw-interface-with
      (interface nothing (w ∷ w' ∷ []))
      (window (suc zero) wp)
  draw-inner w _ (command c) (command cp)
    = draw-interface-with
      (interface (just c) (w ∷ []))
      (command cp)
  draw-inner w _ (both w' c) (both cp)
    = draw-interface-with
      (interface (just c) (w ∷ w' ∷ []))
      (command cp)

  handle
    : (m : Mode)
    → InputEvent
    → Maybe (Event m ⊔ SpecialEvent)
  handle _ InputEvent.escape
    = just (ι₂ SpecialEvent.escape)
  handle _ InputEvent.return
    = just (ι₂ SpecialEvent.return)
  handle _ InputEvent.up
    = just (ι₂ (SpecialEvent.direction Direction.up))
  handle _ InputEvent.down
    = just (ι₂ (SpecialEvent.direction Direction.down))
  handle _ InputEvent.left
    = just (ι₂ (SpecialEvent.direction Direction.left))
  handle _ InputEvent.right
    = just (ι₂ (SpecialEvent.direction Direction.right))
  handle _ (InputEvent.char 'i')
    = just (ι₁ ProofEvent.infer-hypotheses)
  handle _ (InputEvent.char 'm')
    = just (ι₁ ProofEvent.substitute-meta)
  handle _ (InputEvent.char 'q')
    = just (ι₂ SpecialEvent.quit)
  handle _ (InputEvent.char 'w')
    = just (ι₂ SpecialEvent.write)
  handle _ _
    = nothing

  handle-inner
    : (m : ModeInner)
    → InputEvent
    → Maybe (EventInner m ⊔ SpecialEvent)

  handle-inner _ InputEvent.escape
    = just (ι₂ SpecialEvent.escape)
  handle-inner _ InputEvent.return
    = just (ι₂ SpecialEvent.return)
  handle-inner _ InputEvent.up
    = just (ι₂ (SpecialEvent.direction Direction.up))
  handle-inner _ InputEvent.down
    = just (ι₂ (SpecialEvent.direction Direction.down))
  handle-inner _ InputEvent.left
    = just (ι₂ (SpecialEvent.direction Direction.left))
  handle-inner _ InputEvent.right
    = just (ι₂ (SpecialEvent.direction Direction.right))

  handle-inner ProofModeInner.text InputEvent.backspace
    = just (ι₁ TextEvent.delete-previous)
  handle-inner ProofModeInner.text InputEvent.delete
    = just (ι₁ TextEvent.delete-next)
  handle-inner ProofModeInner.text (InputEvent.char c)
    = just (ι₁ (TextEvent.insert c))

  handle-inner ProofModeInner.nat InputEvent.backspace
    = just (ι₁ TextWithEvent.delete-previous)
  handle-inner ProofModeInner.nat InputEvent.delete
    = just (ι₁ TextWithEvent.delete-next)
  handle-inner ProofModeInner.nat (InputEvent.char c)
    with (Char.is-digit? c)
  ... | no _
    = nothing
  ... | yes p
    = just (ι₁ (TextWithEvent.insert (char-with c p)))

  handle-inner ProofModeInner.formula (InputEvent.char '(')
    = just (ι₁ FormulaEvent.insert-parens)
  handle-inner ProofModeInner.formula (InputEvent.char 'v')
    = just (ι₁ FormulaEvent.insert-variable)
  handle-inner ProofModeInner.formula (InputEvent.char 's')
    = just (ι₁ FormulaEvent.insert-symbol)
  handle-inner ProofModeInner.formula _
    = nothing

client-proof
  : Client
    view-stack-proof-window
    event-stack-proof
client-proof
  = record {ClientProof}

-- ## Main

main
  : IO ⊤
main
  = simple-main-editor-run
    "/data/code/prover/test.json"
    (simple-main-editor-proof-window rules ∧-commutative)
    client-proof

