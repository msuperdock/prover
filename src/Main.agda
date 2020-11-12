module Main where

open import Examples
  using (∧-commutative; rules)
open import Prover.Client
  using (Client)
open import Prover.Client.Aeson
  using (Value)
open import Prover.Client.Brick
  using (InputEvent; Widget; draw-interface-with)
open import Prover.Client.Event
  using (SpecialEvent)
open import Prover.Client.Run
  using (simple-main-editor-run)
open import Prover.Data.Formula.Editor
  using (FormulaEvent)
open import Prover.Data.Proof.Editor
  using (ProofEvent; ProofEventStack; ProofModeInner; ProofViewInner;
    ProofViewInnerPath; ProofViewStack; both; command; proof-simple-main-editor;
    window)
open import Prover.Data.Rule
  using (Rule)
open import Prover.Data.Rules
  using (Rules)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text.Editor
  using (TextEvent; TextWithEvent)
open import Prover.Editor
  using (EventStack; SimpleMainEditor; ViewStack; ViewStackMap)
open import Prover.Editor.Map.View
  using (simple-main-editor-map-view-with)
open import Prover.View.Interface
  using (command; interface; nothing; window)
open import Prover.View.Window
  using (Window)
open import Prover.Prelude

open List
  using ([]; _∷_)

-- ## Types

ProofWindowViewStack
  : ViewStack
ProofWindowViewStack
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

module ProofViewStackMap
  (b : Bool)
  where

  view
    : ViewStack.View ProofViewStack
    → ViewStack.View ProofWindowViewStack
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
    : (v : ViewStack.View ProofViewStack)
    → ViewStack.ViewPath ProofViewStack v
    → ViewStack.View ProofWindowViewStack
  view-with v _
    = view v
  
  view-path
    : (v : ViewStack.View ProofViewStack)
    → (vp : ViewStack.ViewPath ProofViewStack v)
    → ViewStack.ViewPath ProofWindowViewStack
      (view-with v vp)
  view-path _
    = id

  view-inner-with
    : (v : ViewStack.View ProofViewStack)
    → (vp : ViewStack.ViewPath ProofViewStack v)
    → (v' : ViewStack.ViewInner ProofViewStack v vp)
    → ViewStack.ViewInnerPath ProofViewStack v vp v'
    → ViewStack.ViewInner ProofWindowViewStack
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ _ v _
    = v

  view-inner-path
    : (v : ViewStack.View ProofViewStack)
    → (vp : ViewStack.ViewPath ProofViewStack v)
    → (v' : ViewStack.ViewInner ProofViewStack v vp)
    → (vp' : ViewStack.ViewInnerPath ProofViewStack v vp v')
    → ViewStack.ViewInnerPath ProofWindowViewStack
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ _ _
    = id

proof-view-stack-map
  : Bool
  → ViewStackMap
    ProofViewStack
    ProofWindowViewStack
proof-view-stack-map b
  = record {ProofViewStackMap b}

proof-window-simple-main-editor
  : {ss : Symbols}
  → Rules ss
  → Rule ss
  → SimpleMainEditor
    ProofWindowViewStack
    ProofEventStack
    Value
proof-window-simple-main-editor rs r
  = simple-main-editor-map-view-with proof-view-stack-map
  $ proof-simple-main-editor rs r

-- ## Client

module ProofClient where

  open ViewStack ProofWindowViewStack
  open EventStack ProofEventStack

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

  handle-inner ProofModeInner.number InputEvent.backspace
    = just (ι₁ TextWithEvent.delete-previous)
  handle-inner ProofModeInner.number InputEvent.delete
    = just (ι₁ TextWithEvent.delete-next)
  handle-inner ProofModeInner.number (InputEvent.char c)
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

proof-client
  : Client
    ProofWindowViewStack
    ProofEventStack
proof-client
  = record {ProofClient}

-- ## Main

main
  : IO ⊤
main
  = simple-main-editor-run
    "/data/code/prover/test.json"
    (proof-window-simple-main-editor rules ∧-commutative)
    proof-client

