module Prover.Editor.Sigma where

open import Prover.Category
  using (Category)
open import Prover.Category.Dependent1
  using (Dependent₁Category)
open import Prover.Category.Sigma
  using (module CategorySigma)
open import Prover.Category.Sigma.Sum
  using (category-sigma-sum)
open import Prover.Category.Sum
  using (module CategorySum)
open import Prover.Editor
  using (Editor; EventStack; SplitEditor; ViewStack; ViewStackMap)
open import Prover.Prelude

-- ## Stacks

-- ### ViewStack

module ViewStackSigma
  (V₁ V₂ : ViewStack)
  where

  View
    : Set
  View
    = ViewStack.View V₁
    × Maybe (ViewStack.View V₂)

  ViewPath
    : View
    → Set
  ViewPath (v₁ , nothing)
    = ViewStack.ViewPath V₁ v₁
  ViewPath (v₁ , just v₂)
    = ViewStack.ViewPath V₁ v₁
    ⊔ ViewStack.ViewPath V₂ v₂
  
  ViewInner
    : (v : View)
    → ViewPath v
    → Set
  ViewInner (v₁ , nothing) vp₁
    = ViewStack.ViewInner V₁ v₁ vp₁
  ViewInner (_ , just _) (ι₁ _)
    = v₁ ∈ ViewStack.View V₁
    × Maybe (Σ (ViewStack.ViewPath V₁ v₁) (ViewStack.ViewInner V₁ v₁))
  ViewInner (_ , just v₂) (ι₂ vp₂)
    = ViewStack.ViewInner V₂ v₂ vp₂
  
  ViewInnerPath
    : (v : View)
    → (vp : ViewPath v)
    → ViewInner v vp
    → Set
  ViewInnerPath (v₁ , nothing) vp₁ v₁'
    = ViewStack.ViewInnerPath V₁ v₁ vp₁ v₁'
  ViewInnerPath (_ , just _) (ι₁ _) (v₁ , nothing)
    = ViewStack.ViewPath V₁ v₁
  ViewInnerPath (_ , just _) (ι₁ _) (v₁ , just (vp₁ , v₁'))
    = ViewStack.ViewInnerPath V₁ v₁ vp₁ v₁'
  ViewInnerPath (_ , just v₂) (ι₂ vp₂) v₂'
    = ViewStack.ViewInnerPath V₂ v₂ vp₂ v₂'

view-stack-sigma
  : ViewStack
  → ViewStack
  → ViewStack
view-stack-sigma V₁ V₂
  = record {ViewStackSigma V₁ V₂}

-- ### EventStack

module EventStackSigma
  (E₁ E₂ : EventStack)
  where

  Mode
    : Set
  Mode
    = EventStack.Mode E₁
    ⊔ EventStack.Mode E₂

  ModeInner
    : Set
  ModeInner
    = EventStack.Mode E₁
    ⊔ EventStack.ModeInner E₁
    ⊔ EventStack.ModeInner E₂

  Event
    : Mode
    → Set
  Event (ι₁ m₁)
    = EventStack.Event E₁ m₁
  Event (ι₂ m₂)
    = EventStack.Event E₂ m₂

  EventInner
    : ModeInner
    → Set
  EventInner (ι₁ m₁)
    = EventStack.Event E₁ m₁
  EventInner (ι₂ (ι₁ m₁))
    = EventStack.EventInner E₁ m₁
  EventInner (ι₂ (ι₂ m₂))
    = EventStack.EventInner E₂ m₂

event-stack-sigma
  : EventStack
  → EventStack
  → EventStack
event-stack-sigma E₁ E₂
  = record {EventStackSigma E₁ E₂}

-- ## Editor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {C₁ : Category}
  where

  -- ### Module

  module EditorSigma
    (C₂ : Dependent₁Category C₁)
    (d : Direction)
    (e₁ : SplitEditor V₁ E₁ C₁)
    (e₂ : (x₁ : Category.Object C₁)
      → Editor V₂ E₂ (Dependent₁Category.category C₂ x₁))
    where

    -- #### Types

    open ViewStack (view-stack-sigma V₁ V₂)
    open EventStack (event-stack-sigma E₁ E₂)

    StateCategory
      : Category
    StateCategory
      = category-sigma-sum C₂
        (SplitEditor.split-functor e₁)

    open Category StateCategory using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      )

    -- #### State

    StatePath
      : State
      → Set
    StatePath (ι₁ s₁)
      = SplitEditor.StatePath e₁ s₁
    StatePath (ι₂ (x₁ , s₂))
      = SplitEditor.StatePath e₁ (SplitEditor.unbase e₁ x₁)
      ⊔ Editor.StatePath (e₂ x₁) s₂

    StateInner
      : (s : State)
      → StatePath s
      → Set
    StateInner (ι₁ s₁) sp₁
      = SplitEditor.StateInner e₁ s₁ sp₁
    StateInner (ι₂ (x₁ , _)) (ι₁ _)
      = s₁ ∈ SplitEditor.State e₁
      × f₁ ∈ SplitEditor.StateArrow e₁ (SplitEditor.unbase e₁ x₁) s₁
      × Maybe (Σ (SplitEditor.StatePath e₁ s₁) (SplitEditor.StateInner e₁ s₁))
    StateInner (ι₂ (x₁ , s₂)) (ι₂ sp₂)
      = Editor.StateInner (e₂ x₁) s₂ sp₂

    StateInnerPath
      : (s : State)
      → (sp : StatePath s)
      → StateInner s sp
      → Set
    StateInnerPath (ι₁ s₁) sp₁ s₁'
      = SplitEditor.StateInnerPath e₁ s₁ sp₁ s₁'
    StateInnerPath (ι₂ _) (ι₁ _) (s₁ , _ , nothing)
      = SplitEditor.StatePath e₁ s₁
    StateInnerPath (ι₂ _) (ι₁ _) (s₁ , _ , just (sp₁ , s₁'))
      = SplitEditor.StateInnerPath e₁ s₁ sp₁ s₁'
    StateInnerPath (ι₂ (x₁ , s₂)) (ι₂ sp₂) s₂'
      = Editor.StateInnerPath (e₂ x₁) s₂ sp₂ s₂'

    StateStack
      : ViewStack
    StateStack
      = record
      { View
        = State
      ; ViewPath
        = StatePath
      ; ViewInner
        = StateInner
      ; ViewInnerPath
        = StateInnerPath
      }

    initial
      : State
    initial
      = ι₁ (SplitEditor.initial e₁)

    initial-path
      : (s : State)
      → StatePath s
    initial-path (ι₁ s₁)
      = SplitEditor.initial-path e₁ s₁
    initial-path (ι₂ (x₁ , _))
      = ι₁ (SplitEditor.initial-path e₁ (SplitEditor.unbase e₁ x₁))

    initial-path-with
      : (s : State)
      → Direction
      → StatePath s
    initial-path-with (ι₁ s₁) d'
      = SplitEditor.initial-path-with e₁ s₁ d'
    initial-path-with (ι₂ (x₁ , s₂)) d'
      with d' ≟ d dir
    ... | no _
      = ι₁ (SplitEditor.initial-path-with e₁ (SplitEditor.unbase e₁ x₁) d')
    ... | yes _
      = ι₂ (Editor.initial-path-with (e₂ x₁) s₂ d')

    -- #### Draw

    draw
      : State
      → View
    draw (ι₁ s₁)
      = (SplitEditor.draw e₁ s₁ , nothing)
    draw (ι₂ (x₁ , s₂))
      = (SplitEditor.draw e₁ (SplitEditor.unbase e₁ x₁)
        , just (Editor.draw (e₂ x₁) s₂))
  
    draw-with
      : (s : State)
      → StatePath s
      → View
    draw-with (ι₁ s₁) sp₁
      = (SplitEditor.draw-with e₁ s₁ sp₁ , nothing)
    draw-with (ι₂ (x₁ , s₂)) (ι₁ sp₁)
      = (SplitEditor.draw-with e₁ (SplitEditor.unbase e₁ x₁) sp₁
        , just (Editor.draw (e₂ x₁) s₂))
    draw-with (ι₂ (x₁ , s₂)) (ι₂ sp₂)
      = (SplitEditor.draw e₁ (SplitEditor.unbase e₁ x₁)
        , just (Editor.draw-with (e₂ x₁) s₂ sp₂))

    draw-path
      : (s : State)
      → (sp : StatePath s)
      → ViewPath (draw-with s sp)
    draw-path (ι₁ s₁) sp₁
      = SplitEditor.draw-path e₁ s₁ sp₁
    draw-path (ι₂ (x₁ , _)) (ι₁ sp₁)
      = ι₁ (SplitEditor.draw-path e₁ (SplitEditor.unbase e₁ x₁) sp₁)
    draw-path (ι₂ (x₁ , s₂)) (ι₂ sp₂)
      = ι₂ (Editor.draw-path (e₂ x₁) s₂ sp₂)

    draw-inner-with
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ViewInner (draw-with s sp) (draw-path s sp)
    draw-inner-with (ι₁ s₁) sp₁ s₁' sp₁'
      = SplitEditor.draw-inner-with e₁ s₁ sp₁ s₁' sp₁'
    draw-inner-with (ι₂ _) (ι₁ _) (s₁ , _ , nothing) sp₁
      = (SplitEditor.draw-with e₁ s₁ sp₁ , nothing)
    draw-inner-with (ι₂ _) (ι₁ _) (s₁' , _ , just (sp₁' , s₁'')) sp₁''
      = (SplitEditor.draw-with e₁ s₁' sp₁'
        , just (SplitEditor.draw-path e₁ s₁' sp₁'
          , SplitEditor.draw-inner-with e₁ s₁' sp₁' s₁'' sp₁''))
    draw-inner-with (ι₂ (x₁ , s₂)) (ι₂ sp₂) s₂' sp₂'
      = Editor.draw-inner-with (e₂ x₁) s₂ sp₂ s₂' sp₂'

    draw-inner-path
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → ViewInnerPath
        (draw-with s sp)
        (draw-path s sp)
        (draw-inner-with s sp s' sp')
    draw-inner-path (ι₁ s₁) sp₁ s₁'
      = SplitEditor.draw-inner-path e₁ s₁ sp₁ s₁'
    draw-inner-path (ι₂ _) (ι₁ _) (s₁ , _ , nothing)
      = SplitEditor.draw-path e₁ s₁
    draw-inner-path (ι₂ _) (ι₁ _) (s₁ , _ , just (sp₁ , s₁'))
      = SplitEditor.draw-inner-path e₁ s₁ sp₁ s₁'
    draw-inner-path (ι₂ (x₁ , s₂)) (ι₂ sp₂) s₂'
      = Editor.draw-inner-path (e₂ x₁) s₂ sp₂ s₂'

    draw-stack
      : ViewStackMap StateStack (view-stack-sigma V₁ V₂)
    draw-stack
      = record
      { view
        = draw
      ; view-with
        = draw-with
      ; view-path
        = draw-path
      ; view-inner-with
        = draw-inner-with
      ; view-inner-path
        = draw-inner-path
      }

    -- #### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode (ι₁ s₁) sp₁
      = ι₁ (SplitEditor.mode e₁ s₁ sp₁)
    mode (ι₂ (x₁ , _)) (ι₁ sp₁)
      = ι₁ (SplitEditor.mode e₁ (SplitEditor.unbase e₁ x₁) sp₁)
    mode (ι₂ (x₁ , s₂)) (ι₂ sp₂)
      = ι₂ (Editor.mode (e₂ x₁) s₂ sp₂)

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner (ι₁ s₁) sp₁ s₁' sp₁'
      = ι₂ (ι₁ (SplitEditor.mode-inner e₁ s₁ sp₁ s₁' sp₁'))
    mode-inner (ι₂ _) (ι₁ _) (s₁ , _ , nothing) sp₁
      = ι₁ (SplitEditor.mode e₁ s₁ sp₁)
    mode-inner (ι₂ _) (ι₁ _) (s₁ , _ , just (sp₁ , s₁')) sp₁'
      = ι₂ (ι₁ (SplitEditor.mode-inner e₁ s₁ sp₁ s₁' sp₁'))
    mode-inner (ι₂ (x₁ , s₂)) (ι₂ sp₂) s₂' sp₂'
      = ι₂ (ι₂ (Editor.mode-inner (e₂ x₁) s₂ sp₂ s₂' sp₂'))

    -- #### Handle

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle (ι₁ s₁) sp₁ e₁'
      with SplitEditor.handle e₁ s₁ sp₁ e₁'
    ... | ι₁ (s₁' , sp₁' , f₁)
      = ι₁ (ι₁ s₁' , sp₁' , CategorySum.arrow₁ f₁)
    ... | ι₂ s₁'
      = ι₂ s₁'
    handle (ι₂ (x₁ , _)) (ι₁ sp₁) e₁'
      with SplitEditor.handle e₁ (SplitEditor.unbase e₁ x₁) sp₁ e₁'
    ... | ι₁ (s₁' , sp₁' , f₁)
      = ι₂ ((s₁' , f₁ , nothing) , sp₁')
    ... | ι₂ (s₁' , sp₁')
      = ι₂ ((SplitEditor.unbase e₁ x₁
        , SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)
        , just (sp₁ , s₁'))
        , sp₁')
    handle (ι₂ (x₁ , s₂)) (ι₂ sp₂) e₂'
      with Editor.handle (e₂ x₁) s₂ sp₂ e₂'
    ... | ι₁ (s₂' , sp₂' , f₂)
      = ι₁ (ι₂ (x₁ , s₂')
        , ι₂ sp₂'
        , CategorySum.arrow₂
          (CategorySigma.arrow s₂
            (Category.identity C₁ x₁)
            (just f₂)
            (Dependent₁Category.base-identity C₂ x₁ s₂)))
    ... | ι₂ s₂'
      = ι₂ s₂'

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape (ι₁ s₁) sp₁
      with SplitEditor.handle-escape e₁ s₁ sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₁ (ι₁ s₁' , sp₁' , CategorySum.arrow₁ f₁))
    ... | just (ι₂ s₁')
      = just (ι₂ s₁')
    handle-escape (ι₂ (x₁ , _)) (ι₁ sp₁)
      with SplitEditor.handle-escape e₁ (SplitEditor.unbase e₁ x₁) sp₁
    ... | nothing
      = just (ι₁ (ι₁ (SplitEditor.unbase e₁ x₁) , sp₁
        , CategorySum.arrow₁
          (SplitEditor.state-identity e₁
            (SplitEditor.unbase e₁ x₁))))
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₁ (ι₁ s₁' , sp₁' , CategorySum.arrow₁ f₁))
    ... | just (ι₂ (s₁' , sp₁'))
      = just (ι₂ ((SplitEditor.unbase e₁ x₁
        , SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)
        , just (sp₁ , s₁'))
        , sp₁'))
    handle-escape (ι₂ (x₁ , s₂)) (ι₂ sp₂)
      with Editor.handle-escape (e₂ x₁) s₂ sp₂
    ... | nothing
      = just (ι₁ (ι₁ (SplitEditor.unbase e₁ x₁)
        , SplitEditor.initial-path e₁ (SplitEditor.unbase e₁ x₁)
        , CategorySum.arrow₁
          (SplitEditor.state-identity e₁
            (SplitEditor.unbase e₁ x₁))))
    ... | just (ι₁ (s₂' , sp₂' , f₂))
      = just (ι₁ (ι₂ (x₁ , s₂')
        , ι₂ sp₂'
        , CategorySum.arrow₂
          (CategorySigma.arrow s₂
            (Category.identity C₁ x₁)
            (just f₂)
            (Dependent₁Category.base-identity C₂ x₁ s₂))))
    ... | just (ι₂ s₂')
      = just (ι₂ s₂')

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return (ι₁ s₁) sp₁
      with SplitEditor.handle-return e₁ s₁ sp₁
      | SplitEditor.base e₁ s₁
      | inspect (SplitEditor.base e₁) s₁
    ... | nothing | nothing | _
      = nothing
    ... | nothing | just x₁ | [ p₁ ]
      = just (ι₁ (ι₂ (x₁ , Editor.initial (e₂ x₁))
        , ι₂ (Editor.initial-path' (e₂ x₁))
        , CategorySum.arrow₁ (SplitEditor.normalize-arrow e₁ s₁ p₁)))
    ... | just (ι₁ (s₁' , sp₁' , f₁)) | _ | _
      = just (ι₁ (ι₁ s₁' , sp₁' , CategorySum.arrow₁ f₁))
    ... | just (ι₂ s₁') | _ | _
      = just (ι₂ s₁')
    handle-return (ι₂ (x₁ , _)) (ι₁ sp₁)
      with SplitEditor.handle-return e₁ (SplitEditor.unbase e₁ x₁) sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₂ ((s₁' , f₁ , nothing) , sp₁'))
    ... | just (ι₂ (s₁' , sp₁'))
      = just (ι₂ ((SplitEditor.unbase e₁ x₁
        , SplitEditor.state-identity e₁ (SplitEditor.unbase e₁ x₁)
        , just (sp₁ , s₁'))
        , sp₁'))
    handle-return (ι₂ (x₁ , s₂)) (ι₂ sp₂)
      with Editor.handle-return (e₂ x₁) s₂ sp₂
    ... | nothing
      = nothing
    ... | just (ι₁ (s₂' , sp₂' , f₂))
      = just (ι₁ (ι₂ (x₁ , s₂')
        , ι₂ sp₂'
        , CategorySum.arrow₂
          (CategorySigma.arrow s₂
            (Category.identity C₁ x₁)
            (just f₂)
            (Dependent₁Category.base-identity C₂ x₁ s₂))))
    ... | just (ι₂ s₂')
      = just (ι₂ s₂')

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)
    handle-direction (ι₁ s₁) sp₁ d'
      = SplitEditor.handle-direction e₁ s₁ sp₁ d'
    handle-direction (ι₂ (x₁ , s₂)) (ι₁ sp₁) d'
      with SplitEditor.handle-direction e₁ (SplitEditor.unbase e₁ x₁) sp₁ d'
      | d' ≟ d dir
    ... | nothing | no _
      = nothing
    ... | nothing | yes _
      = just (ι₂ (Editor.initial-path-with (e₂ x₁) s₂ (Direction.reverse d')))
    ... | just sp₁' | _
      = just (ι₁ sp₁')
    handle-direction (ι₂ (x₁ , s₂)) (ι₂ sp₂) d'
      with Editor.handle-direction (e₂ x₁) s₂ sp₂ d'
      | Direction.reverse d' ≟ d dir
    ... | nothing | no _
      = nothing
    ... | nothing | yes _
      = just (ι₁ (SplitEditor.initial-path-with e₁ (SplitEditor.unbase e₁ x₁)
        (Direction.reverse d')))
    ... | just sp₂' | _
      = just (ι₂ sp₂')

    handle-direction-valid
      : (s : State)
      → (d : Direction)
      → handle-direction s (initial-path-with s d) d ≡ nothing
    handle-direction-valid (ι₁ s₁) d'
      = SplitEditor.handle-direction-valid e₁ s₁ d'
    handle-direction-valid (ι₂ _) d'
      with d' ≟ d dir
      | inspect (_≟_dir d') d
    handle-direction-valid (ι₂ (x₁ , _)) d' | no _ | [ _ ]
      with SplitEditor.handle-direction e₁ (SplitEditor.unbase e₁ x₁)
        (SplitEditor.initial-path-with e₁ (SplitEditor.unbase e₁ x₁) d') d'
      | SplitEditor.handle-direction-valid e₁ (SplitEditor.unbase e₁ x₁) d'
      | d' ≟ d dir
    handle-direction-valid _ _ _ | _ | [ refl ] | _ | refl | _
      = refl
    handle-direction-valid (ι₂ (x₁ , s₂)) d' | yes refl | _
      with Editor.handle-direction (e₂ x₁) s₂
        (Editor.initial-path-with (e₂ x₁) s₂ d') d'
      | Editor.handle-direction-valid (e₂ x₁) s₂ d'
      | Direction.reverse d' ≟ d dir
    ... | _ | refl | no _
      = refl
    ... | _ | _ | yes p
      = ⊥-elim (Direction.reverse-≢ d' p)

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner (ι₁ s₁) sp₁ s₁' sp₁' e₁'
      = SplitEditor.handle-inner e₁ s₁ sp₁ s₁' sp₁' e₁'
    handle-inner (ι₂ _) (ι₁ _) (s₁ , f₁ , nothing) sp₁ e₁'
      with SplitEditor.handle e₁ s₁ sp₁ e₁'
    ... | ι₁ (s₁' , sp₁' , f₁')
      = ((s₁' , SplitEditor.state-compose e₁ f₁' f₁ , nothing) , sp₁')
    ... | ι₂ (s₁' , sp₁')
      = ((s₁ , f₁ , just (sp₁ , s₁')) , sp₁')
    handle-inner (ι₂ _) (ι₁ _) (s₁ , f₁ , just (sp₁ , s₁')) sp₁' e₁'
      with SplitEditor.handle-inner e₁ s₁ sp₁ s₁' sp₁' e₁'
    ... | (s₁'' , sp₁'')
      = ((s₁ , f₁ , just (sp₁ , s₁'')) , sp₁'')
    handle-inner (ι₂ (x₁ , s₂)) (ι₂ sp₂) s₂' sp₂' e₂'
      = Editor.handle-inner (e₂ x₁) s₂ sp₂ s₂' sp₂' e₂'

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape (ι₁ s₁) sp₁ s₁' sp₁'
      = SplitEditor.handle-inner-escape e₁ s₁ sp₁ s₁' sp₁'
    handle-inner-escape (ι₂ _) (ι₁ _) (s₁ , f₁ , nothing) sp₁
      with SplitEditor.handle-escape e₁ s₁ sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁'))
      = just ((s₁' , SplitEditor.state-compose e₁ f₁' f₁ , nothing) , sp₁')
    ... | just (ι₂ (s₁' , sp₁'))
      = just ((s₁ , f₁ , just (sp₁ , s₁')) , sp₁')
    handle-inner-escape (ι₂ _) (ι₁ _) (s₁ , f₁ , just (sp₁ , s₁')) sp₁'
      with SplitEditor.handle-inner-escape e₁ s₁ sp₁ s₁' sp₁'
    ... | nothing
      = just ((s₁ , f₁ , nothing) , sp₁)
    ... | just (s₁'' , sp₁'')
      = just ((s₁ , f₁ , just (sp₁ , s₁'')) , sp₁'')
    handle-inner-escape (ι₂ (x₁ , s₂)) (ι₂ sp₂) s₂' sp₂'
      = Editor.handle-inner-escape (e₂ x₁) s₂ sp₂ s₂' sp₂'

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return (ι₁ s₁) sp₁ s₁' sp₁'
      with SplitEditor.handle-inner-return e₁ s₁ sp₁ s₁' sp₁'
    ... | ι₁ (s₁'' , sp₁'' , f₁)
      = ι₁ (ι₁ s₁'' , sp₁'' , CategorySum.arrow₁ f₁)
    ... | ι₂ s₁''
      = ι₂ s₁''
    handle-inner-return (ι₂ (x₁ , s₂)) (ι₁ _) (s₁ , f₁ , nothing) sp₁
      with SplitEditor.handle-return e₁ s₁ sp₁
      | SplitEditor.base e₁ s₁
      | inspect (SplitEditor.base e₁) s₁
    ... | nothing | nothing | _
      = ι₁ (ι₁ s₁ , sp₁ , CategorySum.arrow₁ f₁)
    ... | nothing | just x₁' | [ p₁ ]
      = ι₁ (ι₂ (x₁' , s₂')
        , ι₂ (Editor.initial-path-with (e₂ x₁') s₂' (Direction.reverse d))
        , CategorySum.arrow₂
          (CategorySigma.arrow s₂' f₁'
            (just (Dependent₁Category.identity C₂ x₁' s₂')) refl))
      where
        f₁' = SplitEditor.map e₁ (SplitEditor.base-unbase e₁ x₁) p₁ f₁
        s₂' = Dependent₁Category.base C₂ f₁' s₂
    ... | just (ι₁ (s₁' , sp₁' , f₁')) | _ | _
      = ι₂ ((s₁' , SplitEditor.state-compose e₁ f₁' f₁ , nothing) , sp₁')
    ... | just (ι₂ (s₁' , sp₁')) | _ | _
      = ι₂ ((s₁ , f₁ , just (sp₁ , s₁')) , sp₁')
    handle-inner-return (ι₂ _) (ι₁ _) (s₁ , f₁ , just (sp₁ , s₁')) sp₁'
      with SplitEditor.handle-inner-return e₁ s₁ sp₁ s₁' sp₁'
    ... | ι₁ (s₁'' , sp₁'' , f₁')
      = ι₂ ((s₁'' , SplitEditor.state-compose e₁ f₁' f₁ , nothing) , sp₁'')
    ... | ι₂ (s₁'' , sp₁'')
      = ι₂ ((s₁ , f₁ , just (sp₁ , s₁'')) , sp₁'')
    handle-inner-return (ι₂ (x₁ , s₂)) (ι₂ sp₂) s₂' sp₂'
      with Editor.handle-inner-return (e₂ x₁) s₂ sp₂ s₂' sp₂'
    ... | ι₁ (s₂'' , sp₂'' , f₂)
      = ι₁ (ι₂ (x₁ , s₂'')
        , ι₂ sp₂''
        , CategorySum.arrow₂
          (CategorySigma.arrow s₂
            (Category.identity C₁ x₁)
            (just f₂)
            (Dependent₁Category.base-identity C₂ x₁ s₂)))
    ... | ι₂ s₂''
      = ι₂ s₂''

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction (ι₁ s₁) sp₁ s₁' sp₁' d'
      = SplitEditor.handle-inner-direction e₁ s₁ sp₁ s₁' sp₁' d'
    handle-inner-direction (ι₂ _) (ι₁ _) (s₁ , _ , nothing) sp₁ d'
      = maybe (SplitEditor.handle-direction e₁ s₁ sp₁ d') sp₁ id
    handle-inner-direction (ι₂ _) (ι₁ _) (s₁ , _ , just (sp₁ , s₁')) sp₁' d'
      = SplitEditor.handle-inner-direction e₁ s₁ sp₁ s₁' sp₁' d'
    handle-inner-direction (ι₂ (x₁ , s₂)) (ι₂ sp₂) s₂' sp₂' d'
      = Editor.handle-inner-direction (e₂ x₁) s₂ sp₂ s₂' sp₂' d'

  -- ### Function

  -- Takes direction from first to second component.
  editor-sigma
    : (C₂ : Dependent₁Category C₁)
    → Direction
    → (e₁ : SplitEditor V₁ E₁ C₁)
    → ((x₁ : Category.Object C₁)
      → Editor V₂ E₂ (Dependent₁Category.category C₂ x₁))
    → Editor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (category-sigma-sum C₂ (SplitEditor.split-functor e₁))
  editor-sigma C₂ d e₁ e₂
    = record {EditorSigma C₂ d e₁ e₂}

