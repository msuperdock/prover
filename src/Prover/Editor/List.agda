module Prover.Editor.List where

open import Prover.Category
  using (Category)
open import Prover.Category.List
  using (module CategoryList; category-list)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Category.Split.List
  using (split-functor-list)
open import Prover.Editor
  using (Editor; EventStack; MainEditor; PartialEditor; SimpleEditor;
    SplitEditor; SplitMainEditor; ViewStack; ViewStackMap; any)
open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Function.Bool.List
  using (bool-function-list)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Partial.List
  using (partial-function-list)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Function.Split.List
  using (split-function-list)
open import Prover.Prelude

open List
  using ([]; _∷_; _!_)

-- ## Stacks

-- ### ViewStack

module ViewStackList
  (V : ViewStack)
  where

  View
    : Set
  View
    = List
      (ViewStack.View V)

  ViewPath
    : View
    → Set
  ViewPath (any {zero} _)
    = ⊤
  ViewPath vs@(any {suc _} _)
    = k ∈ Fin (List.length vs)
    × ViewStack.ViewPath V (vs ! k)
  
  ViewInner
    : (v : View)
    → ViewPath v
    → Set
  ViewInner (any {zero} _) _
    = ⊥
  ViewInner vs@(any {suc _} _) (k , vp)
    = ViewStack.ViewInner V (vs ! k) vp

  ViewInnerPath
    : (v : View)
    → (vp : ViewPath v)
    → ViewInner v vp
    → Set
  ViewInnerPath vs@(any {suc _} _) (k , vp)
    = ViewStack.ViewInnerPath V (vs ! k) vp

view-stack-list
  : ViewStack
  → ViewStack
view-stack-list V
  = record {ViewStackList V}

-- ### EventStack

data ListEvent
  : Set
  where

  insert-before
    : ListEvent

  insert-after
    : ListEvent

  delete
    : ListEvent

  move-previous
    : ListEvent

  move-next
    : ListEvent

data ListEventEmpty
  : Set
  where

  insert
    : ListEventEmpty

module EventStackList
  (E : EventStack)
  where

  open EventStack E public
    using (ModeInner; EventInner)

  Mode
    : Set
  Mode
    = Maybe (EventStack.Mode E)

  Event
    : Mode
    → Set
  Event nothing
    = ListEventEmpty
  Event (just m)
    = EventStack.Event E m ⊔ ListEvent

event-stack-list
  : EventStack
  → EventStack
event-stack-list E
  = record {EventStackList E}

-- ## StackMaps

-- ### ViewStackMap

module _
  {V W : ViewStack}
  where

  module ViewStackMapList
    (F : ViewStackMap V W)
    where

    view
      : ViewStack.View (view-stack-list V)
      → ViewStack.View (view-stack-list W)
    view
      = List.map (ViewStackMap.view F)

    view-with
      : (v : ViewStack.View (view-stack-list V))
      → ViewStack.ViewPath (view-stack-list V) v
      → ViewStack.View (view-stack-list W)
    view-with [] _
      = []
    view-with (v ∷ vs) (zero , vp)
      = ViewStackMap.view-with F v vp ∷ view vs
    view-with (v ∷ vs@(_ ∷ _)) (suc k , vp)
      = ViewStackMap.view F v ∷ view-with vs (k , vp)
    
    view-path
      : (v : ViewStack.View (view-stack-list V))
      → (vp : ViewStack.ViewPath (view-stack-list V) v)
      → ViewStack.ViewPath (view-stack-list W)
        (view-with v vp)
    view-path [] _
      = tt
    view-path (v ∷ _) (zero , vp)
      = (zero , ViewStackMap.view-path F v vp)
    view-path (_ ∷ v ∷ _) (suc zero , vp)
      = (suc zero , ViewStackMap.view-path F v vp)
    view-path (_ ∷ vs@(_ ∷ _ ∷ _)) (suc k@(suc _) , vp)
      with view-path vs (k , vp)
    ... | (k' , vp')
      = (suc k' , vp')

    view-inner-with
      : (v : ViewStack.View (view-stack-list V))
      → (vp : ViewStack.ViewPath (view-stack-list V) v)
      → (v' : ViewStack.ViewInner (view-stack-list V) v vp)
      → ViewStack.ViewInnerPath (view-stack-list V) v vp v'
      → ViewStack.ViewInner (view-stack-list W)
        (view-with v vp)
        (view-path v vp)
    view-inner-with (v ∷ _) (zero , vp)
      = ViewStackMap.view-inner-with F v vp
    view-inner-with (_ ∷ v ∷ _) (suc zero , vp)
      = ViewStackMap.view-inner-with F v vp
    view-inner-with (_ ∷ vs@(_ ∷ _ ∷ _)) (suc k@(suc _) , vp)
      = view-inner-with vs (k , vp)

    view-inner-path
      : (v : ViewStack.View (view-stack-list V))
      → (vp : ViewStack.ViewPath (view-stack-list V) v)
      → (v' : ViewStack.ViewInner (view-stack-list V) v vp)
      → (vp' : ViewStack.ViewInnerPath (view-stack-list V) v vp v')
      → ViewStack.ViewInnerPath (view-stack-list W)
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')
    view-inner-path (v ∷ _) (zero , vp)
      = ViewStackMap.view-inner-path F v vp
    view-inner-path (_ ∷ v ∷ _) (suc zero , vp)
      = ViewStackMap.view-inner-path F v vp
    view-inner-path (_ ∷ vs@(_ ∷ _ ∷ _)) (suc k@(suc _) , vp)
      = view-inner-path vs (k , vp)

  view-stack-map-list
    : ViewStackMap V W
    → ViewStackMap
      (view-stack-list V)
      (view-stack-list W)
  view-stack-map-list F
    = record {ViewStackMapList F}

-- ## Editors

-- ### Editor

module _
  {V : ViewStack}
  {E : EventStack}
  {C : Category}
  where

  -- #### Module

  module EditorList
    (d : Direction)
    (e : Editor V E C)
    where

    -- ##### Types
  
    open EventStack (event-stack-list E)

    open Category (category-list C) using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      )

    -- ##### State

    StateStack
      : ViewStack
    StateStack
      = view-stack-list
        (Editor.StateStack e)

    open ViewStack StateStack using () renaming
      ( ViewPath
        to StatePath
      ; ViewInner
        to StateInner
      ; ViewInnerPath
        to StateInnerPath
      )

    initial
      : State
    initial
      = []

    initial-path
      : (s : State)
      → StatePath s
    initial-path []
      = tt
    initial-path (s ∷ _)
      = (zero , Editor.initial-path e s)

    initial-path-with
      : (s : State)
      → Direction
      → StatePath s
    initial-path-with [] _
      = tt
    initial-path-with ss@(s ∷ ss') d'
      with d' ≟ d dir
    ... | no _
      = zero
      , Editor.initial-path-with e s d'
    ... | yes _
      = Fin.maximum (List.length ss')
      , Editor.initial-path-with e (ss ! Fin.maximum (List.length ss')) d'

    -- ##### Draw

    draw-stack
      : ViewStackMap StateStack (view-stack-list V)
    draw-stack
      = view-stack-map-list
        (Editor.draw-stack e)

    -- ##### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode (any {zero} _) _
      = nothing
    mode ss@(any {suc _} _) (k , sp)
      = just (Editor.mode e (ss ! k) sp)

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner ss@(_ ∷ _) (k , sp)
      = Editor.mode-inner e (ss ! k) sp

    -- ##### Handle

    handle-insert
      : (s : State)
      → Fin (suc (List.length s))
      → s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
    handle-insert ss k
      = List.insert ss k (Editor.initial e)
      , (k , rewrite'
        (Editor.StatePath e)
        (List.lookup-insert ss k (Editor.initial e))
        (Editor.initial-path' e))
      , CategoryList.insert C ss k (Editor.initial e)

    handle-update
      : (s : State)
      → (k : Fin (List.length s))
      → (s' : Category.Object C)
      → (sp' : Editor.StatePath e s')
      → Category.Arrow C (s ! k) s'
      → s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
    handle-update ss@(_ ∷ _) k s' sp' f
      = List.update ss k s'
      , (k , rewrite'
        (Editor.StatePath e)
        (List.lookup-update ss k s') sp')
      , CategoryList.update C ss k f

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle ss@[] _ insert
      = ι₁ (handle-insert ss zero)
    handle ss@(_ ∷ _) (k , _) (ι₂ insert-before)
      = ι₁ (handle-insert ss (Fin.lift k))
    handle ss@(_ ∷ _) (k , _) (ι₂ insert-after)
      = ι₁ (handle-insert ss (suc k))

    handle ss@(_ ∷ _) (k , sp) (ι₁ e')
      with Editor.handle e (ss ! k) sp e'
    ... | ι₁ (s' , sp' , f)
      = ι₁ (handle-update ss k s' sp' f)
    ... | ι₂ s'
      = ι₂ s'

    handle ss@(_ ∷ []) _ (ι₂ delete)
      = ι₁ ([]
        , tt
        , CategoryList.delete C ss zero)
    handle ss@(_ ∷ ss'@(s ∷ _)) (zero , _) (ι₂ delete)
      = ι₁ (ss'
        , (zero , Editor.initial-path e s)
        , CategoryList.delete C ss zero)
    handle ss@(_ ∷ _ ∷ _) (suc k , _) (ι₂ delete)
      = ι₁ (List.delete ss (suc k)
        , (k , Editor.initial-path e (List.delete ss (suc k) ! k))
        , CategoryList.delete C ss (suc k))

    handle ss@(_ ∷ _) sp@(zero , _) (ι₂ move-previous)
      = ι₁ (ss , sp , Category.identity (category-list C) ss)
    handle (s ∷ ss) (suc k , sp) (ι₂ move-previous)
      = ι₁ (List.swap s ss k
        , (Fin.lift k , rewrite'
          (Editor.StatePath e)
          (List.lookup-swap₁ s ss k) sp)
        , CategoryList.swap C s ss k)

    handle (_ ∷ _) (k , _) (ι₂ move-next)
      with Fin.drop k
      | inspect Fin.drop k
    handle ss sp _ | nothing | _
      = ι₁ (ss , sp , Category.identity (category-list C) ss)
    handle (s ∷ ss) (k , sp) _ | just k' | [ p ]
      = ι₁ (List.swap s ss k'
        , (suc k' , rewrite'
          (Editor.StatePath e)
          (List.lookup-swap₂' s ss k p) sp)
        , CategoryList.swap C s ss k')

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape [] _
      = nothing
    handle-escape ss@(_ ∷ _) (k , sp)
      with Editor.handle-escape e (ss ! k) sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , f))
      = just (ι₁ (handle-update ss k s' sp' f))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return [] _
      = nothing
    handle-return ss@(_ ∷ _) (k , sp)
      with Editor.handle-return e (ss ! k) sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , f))
      = just (ι₁ (handle-update ss k s' sp' f))
    ... | just (ι₂ s')
      = just (ι₂ s')

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)
    handle-direction [] _ _
      = nothing
    handle-direction ss@(_ ∷ _) (k , sp) d'
      with Editor.handle-direction e (ss ! k) sp d'
      | d' ≟ d dir
      | Direction.reverse d' ≟ d dir
      | Fin.increment k
      | Fin.decrement k
    ... | nothing | yes _ | _ | just k' | _
      = just (k' , Editor.initial-path-with e (ss ! k') (Direction.reverse d'))
    ... | nothing | _ | yes _ | _ | just k'
      = just (k' , Editor.initial-path-with e (ss ! k') d')
    ... | nothing | _ | _ | _ | _
      = nothing
    ... | just sp' | _ | _ | _ | _
      = just (k , sp')

    handle-direction-valid
      : (s : State)
      → (d' : Direction)
      → handle-direction s (initial-path-with s d') d' ≡ nothing
    handle-direction-valid [] _
      = refl
    handle-direction-valid (_ ∷ _) d'
      with d' ≟ d dir
    handle-direction-valid (s ∷ _) d' | no _
      with Editor.handle-direction e s
        (Editor.initial-path-with e s d') d'
      | Editor.handle-direction-valid e s d'
      | Direction.reverse d' ≟ d dir
    ... | _ | refl | no _
      = refl
    ... | _ | refl | yes _
      = refl
    handle-direction-valid ss@(_ ∷ ss') d' | yes refl
      with Editor.handle-direction e (ss ! Fin.maximum (List.length ss'))
        (Editor.initial-path-with e (ss ! Fin.maximum (List.length ss')) d') d'
      | Editor.handle-direction-valid e (ss ! Fin.maximum (List.length ss')) d'
      | Fin.increment (Fin.maximum (List.length ss'))
      | Fin.increment-maximum (List.length ss')
      | Direction.reverse d' ≟ d dir
    ... | _ | refl | _ | refl | no _
      = refl
    ... | _ | _ | _ | _ | yes p
      = ⊥-elim (Direction.reverse-≢ d' p)

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner ss@(_ ∷ _) (k , sp)
      = Editor.handle-inner e (ss ! k) sp

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape ss@(_ ∷ _) (k , sp)
      = Editor.handle-inner-escape e (ss ! k) sp

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return ss@(_ ∷ _) (k , sp) s' sp'
      with Editor.handle-inner-return e (ss ! k) sp s' sp'
    ... | ι₁ (s'' , sp'' , f)
      = ι₁ (handle-update ss k s'' sp'' f)
    ... | ι₂ s''
      = ι₂ s''

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction ss@(_ ∷ _) (k , sp)
      = Editor.handle-inner-direction e (ss ! k) sp

  -- #### Function

  -- Takes direction from earlier to later elements.
  editor-list
    : Direction
    → Editor V E C
    → Editor
      (view-stack-list V)
      (event-stack-list E)
      (category-list C)
  editor-list d e
    = record {EditorList d e}

-- ### SimpleEditor

-- Takes direction from earlier to later elements.
simple-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → Direction
  → SimpleEditor V E A
  → SimpleEditor
    (view-stack-list V)
    (event-stack-list E)
    (List A)
simple-editor-list d (any e)
  = any (editor-list d e)

-- ### PartialEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  module PartialEditorList
    (d : Direction)
    (e : PartialEditor V E A)
    where

    State
      : Set
    State
      = List
        (PartialEditor.State e)

    simple-editor
      : SimpleEditor
        (view-stack-list V)
        (event-stack-list E)
        State
    simple-editor
      = simple-editor-list d
        (PartialEditor.simple-editor e)

    partial-function
      : PartialFunction
        State
        (List A)
    partial-function
      = partial-function-list
        (PartialEditor.partial-function e)

  -- Takes direction from earlier to later elements.
  partial-editor-list
    : Direction
    → PartialEditor V E A
    → PartialEditor
      (view-stack-list V)
      (event-stack-list E)
      (List A)
  partial-editor-list d e
    = record {PartialEditorList d e}

-- ### SplitEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {C : Category}
  where

  module SplitEditorList
    (d : Direction)
    (e : SplitEditor V E C)
    where

    StateCategory
      : Category
    StateCategory
      = category-list
        (SplitEditor.StateCategory e)

    editor
      : Editor
        (view-stack-list V)
        (event-stack-list E)
        StateCategory
    editor
      = editor-list d
        (SplitEditor.editor e)

    split-functor
      : SplitFunctor
        StateCategory
        (category-list C)
    split-functor
      = split-functor-list
        (SplitEditor.split-functor e)

  -- Takes direction from earlier to later elements.
  split-editor-list
    : Direction
    → SplitEditor V E C
    → SplitEditor
      (view-stack-list V)
      (event-stack-list E)
      (category-list C)
  split-editor-list d e
    = record {SplitEditorList d e}

-- ### MainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S : Set}
  where

  module MainEditorList
    (d : Direction)
    (e : MainEditor V E S)
    where

    State
      : Set
    State
      = List
        (MainEditor.State e)

    simple-editor
      : SimpleEditor
        (view-stack-list V)
        (event-stack-list E)
        State
    simple-editor
      = simple-editor-list d
        (MainEditor.simple-editor e)

    split-function
      : SplitFunction
        (List S)
        State
    split-function
      = split-function-list
        (MainEditor.split-function e)

    bool-function
      : BoolFunction
        State
    bool-function
      = bool-function-list
        (MainEditor.bool-function e)

  -- Takes direction from earlier to later elements.
  main-editor-list
    : Direction
    → MainEditor V E S
    → MainEditor
      (view-stack-list V)
      (event-stack-list E)
      (List S)
  main-editor-list d e
    = record {MainEditorList d e}

-- ### SplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C : Category}
  where

  module SplitMainEditorList
    (d : Direction)
    (e : SplitMainEditor V E S P C)
    where

    StateCategory
      : Category
    StateCategory
      = category-list
        (SplitMainEditor.StateCategory e)

    open Category StateCategory using () renaming
      ( Object
        to State
      )

    editor
      : Editor
        (view-stack-list V)
        (event-stack-list E)
        StateCategory
    editor
      = editor-list d
        (SplitMainEditor.editor e)

    state-split-function
      : SplitFunction
        (List S)
        State
    state-split-function
      = split-function-list
        (SplitMainEditor.state-split-function e)

    pure-split-function
      : SplitFunction
        (List P)
        (Category.Object (category-list C))
    pure-split-function
      = split-function-list
        (SplitMainEditor.pure-split-function e)

    split-functor
      : SplitFunctor
        StateCategory
        (category-list C)
    split-functor
      = split-functor-list
        (SplitMainEditor.split-functor e)

  -- Takes direction from earlier to later elements.
  split-main-editor-list
    : Direction
    → SplitMainEditor V E S P C
    → SplitMainEditor
      (view-stack-list V)
      (event-stack-list E)
      (List S)
      (List P)
      (category-list C)
  split-main-editor-list d e
    = record {SplitMainEditorList d e}

