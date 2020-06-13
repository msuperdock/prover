module Prover.Data.Formula.Editor where

open import Prover.Category
  using (Category)
open import Prover.Category.Unit
  using (category-unit)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Formula.State
  using (FormulaState; FormulaStatePath; Left; Right; SandboxState;
    SandboxStatePath; center; end; go; left; nothing; right; stop)
open import Prover.Data.Formula.Insert
  using (sandbox-state-insert-parens; sandbox-state-insert-symbol;
    sandbox-state-insert-variable)
open import Prover.Data.Meta.Editor
  using (draw-meta)
open import Prover.Data.Symbol
  using (Symbol)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text.Editor
  using (TextEvent; TextFlatEventStack; command-flat-editor)
open import Prover.Data.Token
  using (Token)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Editor
  using (EventStack; EventStackMap; PartialEditor; SimpleEditor; SplitEditor;
    ViewStack; ViewStackMap; split-editor-partial)
open import Prover.Editor.Base
  using (BaseEventStack; BaseViewStack; SimpleBaseEditor)
open import Prover.Editor.Child
  using (SimpleChildEditor)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatViewStack)
open import Prover.Editor.Map
  using (flat-editor-map; simple-editor-map-event; simple-editor-map-view)
open import Prover.Editor.Parent
  using (event-stack-parent; simple-editor-parent; view-stack-parent)
open import Prover.Editor.Unit
  using (split-editor-unit)
open import Prover.View.Command
  using (Command; CommandFlatViewStack; CommandPath)
open import Prover.View.Text
  using (RichText; RichTextPath; plain; style; text)
open import Prover.Prelude

-- ## Types

-- ### View

FormulaView
  : Set
FormulaView
  = RichText

FormulaViewPath
  : FormulaView
  → Set
FormulaViewPath f
  = Maybe (RichTextPath f)

FormulaViewStack
  : ViewStack
FormulaViewStack
  = record
  { View
    = FormulaView
  ; ViewPath
    = FormulaViewPath
  ; ViewInner
    = λ _ _ → Command
  ; ViewInnerPath
    = λ _ _ → CommandPath
  }

-- ### Event

data FormulaEvent
  : Set
  where

  insert-parens
    : FormulaEvent

  insert-variable
    : FormulaEvent

  insert-symbol
    : FormulaEvent

FormulaEventStack
  : EventStack
FormulaEventStack
  = record
  { Mode
    = ⊤
  ; ModeInner
    = ⊤
  ; Event
    = λ _ → FormulaEvent
  ; EventInner
    = λ _ → TextEvent
  }

-- ### Pure

FormulaCategory
  : Symbols
  → Variables
  → Bool
  → Category
FormulaCategory ss vs m
  = category-unit (Formula ss vs m)

-- ## Draw

module _
  {ss : Symbols}
  {vs : Variables}
  {m : Bool}
  where

  -- ### Types

  draw-formula
    : FormulaState ss vs m
    → RichText
  
  draw-formula-left
    : {a : ℕ}
    → {s : Symbol a}
    → Left ss vs m s
    → RichText

  draw-formula-right
    : {a : ℕ}
    → {s : Symbol a}
    → Right ss vs m s
    → RichText

  draw-formula-center
    : {n : ℕ}
    → Vec Token (suc n)
    → Vec (Any (SandboxState ss vs m)) n
    → RichText

  draw-sandbox
    : Any (SandboxState ss vs m)
    → RichText
  
  draw-formula FormulaState.hole
    = RichText.plain (String.to-vec "_")
  draw-formula (FormulaState.parens s)
    = RichText.wrap "(" ")" (draw-sandbox s)
  draw-formula (FormulaState.meta m)
    = draw-meta (String.to-vec (Nat.show m))
  draw-formula (FormulaState.variable' (any cs) _)
    = RichText.plain (any cs)
  draw-formula (FormulaState.symbol s _ l r cs)
    = RichText.texts
    $ draw-formula-left l
    ∷ draw-formula-center (Symbol.tokens s) cs
    ∷ draw-formula-right r
    ∷ []

  draw-formula-left (nothing _)
    = RichText.plain (any [])
  draw-formula-left (left f _)
    = draw-formula f

  draw-formula-right (nothing _)
    = RichText.plain (any [])
  draw-formula-right (right f _)
    = draw-formula f

  draw-formula-center (t ∷ []) []
    = RichText.plain (any (Token.characters t))
  draw-formula-center (t ∷ ts@(_ ∷ _)) (s ∷ ss)
    = RichText.texts
    $ RichText.plain (any (Token.characters t))
    ∷ draw-sandbox s
    ∷ draw-formula-center ts ss
    ∷ []

  draw-sandbox (any (SandboxState.singleton f))
    = draw-formula f
  draw-sandbox (any (SandboxState.cons f _ s _))
    = RichText.texts
    $ draw-formula f
    ∷ RichText.plain (String.to-vec "   ")
    ∷ draw-sandbox s
    ∷ []

  -- ### Paths

  draw-path-formula
    : (f : FormulaState ss vs m)
    → FormulaStatePath f
    → RichTextPath (draw-formula f)

  draw-path-formula-center-stop
    : {n : ℕ}
    → (ts : Vec Token (suc n))
    → (ss : Vec (Any (SandboxState ss vs m)) n)
    → RichTextPath (draw-formula-center ts ss)

  draw-path-formula-center
    : {n : ℕ}
    → (ts : Vec Token (suc n))
    → (ss : Vec (Any (SandboxState ss vs m)) n)
    → (k : Fin n)
    → SandboxStatePath (ss ! k)
    → RichTextPath (draw-formula-center ts ss)

  draw-path-sandbox
    : (s : Any (SandboxState ss vs m))
    → SandboxStatePath s
    → Maybe (RichTextPath (draw-sandbox s))

  draw-path-sandbox-go
    : (s : Any (SandboxState ss vs m))
    → (k : Fin (SandboxState.length s))
    → FormulaStatePath (SandboxState.lookup s k)
    → RichTextPath (draw-sandbox s)

  draw-path-formula FormulaState.hole stop
    = plain zero
  draw-path-formula (FormulaState.parens _) stop
    = text zero (plain zero)
  draw-path-formula (FormulaState.parens s) (center zero (go k fp))
    = text (suc zero) (draw-path-sandbox-go s k fp)
  draw-path-formula (FormulaState.parens _) (center zero end)
    = text (suc (suc zero)) (plain zero)
  draw-path-formula (FormulaState.meta _) stop
    = style (text zero (plain zero))
  draw-path-formula (FormulaState.variable' _ _) stop
    = plain zero
  draw-path-formula (FormulaState.symbol _ _ (left f _) _ _) (left fp)
    = text zero (draw-path-formula f fp)
  draw-path-formula (FormulaState.symbol s _ _ _ cs) stop
    = text (suc zero) (draw-path-formula-center-stop (Symbol.tokens s) cs)
  draw-path-formula (FormulaState.symbol s _ _ _ cs) (center k sp)
    = text (suc zero) (draw-path-formula-center (Symbol.tokens s) cs k sp)
  draw-path-formula (FormulaState.symbol _ _ _ (right f _) _) (right fp)
    = text (suc (suc zero)) (draw-path-formula f fp)

  draw-path-formula-center-stop (t ∷ []) []
    = plain (Token.index t)
  draw-path-formula-center-stop (t ∷ _ ∷ _) (_ ∷ _)
    = text zero (plain (Token.index t))

  draw-path-formula-center (_ ∷ _ ∷ _) (s ∷ _) zero (go k fp)
    = text (suc zero) (draw-path-sandbox-go s k fp)
  draw-path-formula-center (_ ∷ ts@(_ ∷ _)) (_ ∷ ss) zero end
    = text (suc (suc zero)) (draw-path-formula-center-stop ts ss)
  draw-path-formula-center (_ ∷ ts@(_ ∷ _)) (_ ∷ ss) (suc k) sp
    = text (suc (suc zero)) (draw-path-formula-center ts ss k sp)

  draw-path-sandbox s (go k fp)
    = just (draw-path-sandbox-go s k fp)
  draw-path-sandbox _ end
    = nothing

  draw-path-sandbox-go (any (SandboxState.singleton f)) zero fp
    = draw-path-formula f fp
  draw-path-sandbox-go (any (SandboxState.cons f _ _ _)) zero fp
    = text zero (draw-path-formula f fp)
  draw-path-sandbox-go (any (SandboxState.cons f _ s _)) (suc k) fp
    = text (suc (suc zero)) (draw-path-sandbox-go s k fp)

-- ## Editors

-- ### Base

-- #### View

FormulaBaseViewStack
  : BaseViewStack
FormulaBaseViewStack
  = record
  { View
    = FormulaView
  ; ViewPath
    = FormulaViewPath
  }

-- #### Event

data FormulaBaseEvent
  : Set
  where

  insert-parens
    : FormulaBaseEvent

FormulaBaseEventStack
  : BaseEventStack
FormulaBaseEventStack
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → FormulaBaseEvent
  }

-- #### Module

module FormulaSimpleBaseEditor
  (ss : Symbols)
  (vs : Variables)
  (m : Bool)
  where

  -- ##### Types

  open BaseViewStack FormulaBaseViewStack
  open BaseEventStack FormulaBaseEventStack

  State
    : Set
  State
    = Any (SandboxState ss vs m)

  -- ##### State

  StatePath
    : State
    → Set
  StatePath
    = SandboxStatePath

  initial
    : State
  initial
    = SandboxState.hole

  initial-path
    : (s : State)
    → Direction
    → StatePath s
  initial-path _ Direction.up
    = SandboxStatePath.leftmost
  initial-path _ Direction.down
    = SandboxStatePath.leftmost
  initial-path _ Direction.left
    = SandboxStatePath.leftmost
  initial-path _ Direction.right
    = SandboxStatePath.end

  -- ##### Draw

  draw
    : State
    → View
  draw s
    = draw-sandbox s

  draw-with
    : (s : State)
    → StatePath s
    → View
  draw-with s _
    = draw s

  draw-path
    : (s : State)
    → (sp : StatePath s)
    → ViewPath (draw-with s sp)
  draw-path
    = draw-path-sandbox

  -- ##### Mode

  mode
    : (s : State)
    → StatePath s
    → Mode
  mode _ _
    = tt

  -- ##### Handle

  handle
    : (s : State)
    → (sp : StatePath s)
    → Event (mode s sp)
    → Σ State StatePath
  handle s sp insert-parens
    = sandbox-state-insert-parens s sp

  handle-direction
    : (s : State)
    → StatePath s
    → Direction
    → Maybe (StatePath s)
  handle-direction _ _ Direction.up
    = nothing
  handle-direction _ _ Direction.down
    = nothing
  handle-direction _ sp Direction.left
    = SandboxStatePath.left sp
  handle-direction _ sp Direction.right
    = SandboxStatePath.right sp

  handle-direction-valid
    : (s : State)
    → (d : Direction)
    → handle-direction s (initial-path s d) d ≡ nothing
  handle-direction-valid _ Direction.up
    = refl
  handle-direction-valid _ Direction.down
    = refl
  handle-direction-valid _ Direction.left
    = SandboxStatePath.left-leftmost
  handle-direction-valid _ Direction.right
    = refl

-- #### Editor

formula-simple-base-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleBaseEditor
    FormulaBaseViewStack
    FormulaBaseEventStack
    (Any (SandboxState ss vs m))
formula-simple-base-editor ss vs m
  = record {FormulaSimpleBaseEditor ss vs m}

-- ### Child

-- #### Key

data FormulaKey
  : Set
  where

  variable'
    : FormulaKey

  symbol
    : FormulaKey

-- #### View

FormulaChildViewStack
  : FormulaKey
  → FlatViewStack
FormulaChildViewStack _
  = CommandFlatViewStack

-- #### Event

FormulaChildEventStack
  : FormulaKey
  → FlatEventStack
FormulaChildEventStack _
  = TextFlatEventStack

-- #### Variable

module FormulaSimpleChildEditorVariable
  (ss : Symbols)
  (vs : Variables)
  (m : Bool)
  where

  BaseState
    : Set
  BaseState
    = Any (SandboxState ss vs m)

  open SimpleBaseEditor (formula-simple-base-editor ss vs m) using () renaming
    ( StatePath
      to BaseStatePath
    )

  Result
    : (s : BaseState)
    → BaseStatePath s
    → Set
  Result _ _
    = Variables.Member vs

  flat-editor
    : (s : BaseState)
    → (sp : BaseStatePath s)
    → FlatEditor
      (FormulaChildViewStack variable')
      (FormulaChildEventStack variable')
      (Result s sp)
  flat-editor _ _
    = flat-editor-map (Variables.lookup-member vs)
    $ command-flat-editor "v"

  update
    : (s : BaseState)
    → (sp : BaseStatePath s)
    → Result s sp
    → Σ BaseState BaseStatePath
  update s sp (Variables.member v p)
    = sandbox-state-insert-variable s sp v p

formula-simple-child-editor-variable
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleChildEditor
    (FormulaChildViewStack variable')
    (FormulaChildEventStack variable')
    (formula-simple-base-editor ss vs m)
formula-simple-child-editor-variable ss vs m
  = record {FormulaSimpleChildEditorVariable ss vs m}

-- #### Symbol

module FormulaSimpleChildEditorSymbol
  (ss : Symbols)
  (vs : Variables)
  (m : Bool)
  where

  BaseState
    : Set
  BaseState
    = Any (SandboxState ss vs m)

  open SimpleBaseEditor (formula-simple-base-editor ss vs m) using () renaming
    ( StatePath
      to BaseStatePath
    )

  Result
    : (s : BaseState)
    → BaseStatePath s
    → Set
  Result _ _
    = Symbols.Member ss

  flat-editor
    : (s : BaseState)
    → (sp : BaseStatePath s)
    → FlatEditor
      (FormulaChildViewStack symbol)
      (FormulaChildEventStack symbol)
      (Result s sp)
  flat-editor _ _
    = flat-editor-map (Symbols.lookup-member ss)
    $ command-flat-editor "s"

  update
    : (s : BaseState)
    → (sp : BaseStatePath s)
    → Result s sp
    → Σ BaseState BaseStatePath
  update s sp (Symbols.member s' p)
    = sandbox-state-insert-symbol s sp s' p

formula-simple-child-editor-symbol
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleChildEditor
    (FormulaChildViewStack symbol)
    (FormulaChildEventStack symbol)
    (formula-simple-base-editor ss vs m)
formula-simple-child-editor-symbol ss vs m
  = record {FormulaSimpleChildEditorSymbol ss vs m}

-- #### Editor

formula-simple-child-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → (k : FormulaKey)
  → SimpleChildEditor
    (FormulaChildViewStack k)
    (FormulaChildEventStack k)
    (formula-simple-base-editor ss vs m)
formula-simple-child-editor ss vs m variable'
  = formula-simple-child-editor-variable ss vs m
formula-simple-child-editor ss vs m symbol
  = formula-simple-child-editor-symbol ss vs m

-- ### Parent

-- #### View

FormulaParentViewStack
  : ViewStack
FormulaParentViewStack
  = view-stack-parent
    FormulaBaseViewStack
    FormulaChildViewStack

-- #### Event

FormulaParentEventStack
  : EventStack
FormulaParentEventStack
  = event-stack-parent
    FormulaBaseEventStack
    FormulaChildEventStack

-- #### Editor

formula-simple-parent-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleEditor
    FormulaParentViewStack
    FormulaParentEventStack
    (Any (SandboxState ss vs m))
formula-simple-parent-editor ss vs m
  = simple-editor-parent
    FormulaChildViewStack
    FormulaChildEventStack
    (formula-simple-base-editor ss vs m)
    (formula-simple-child-editor ss vs m)

-- ### Simple

-- #### View

module FormulaViewStackMap where

  view
    : ViewStack.View FormulaParentViewStack
    → ViewStack.View FormulaViewStack
  view
    = id

  view-with
    : (v : ViewStack.View FormulaParentViewStack)
    → ViewStack.ViewPath FormulaParentViewStack v
    → ViewStack.View FormulaViewStack
  view-with v _
    = view v
  
  view-path
    : (v : ViewStack.View FormulaParentViewStack)
    → (vp : ViewStack.ViewPath FormulaParentViewStack v)
    → ViewStack.ViewPath FormulaViewStack
      (view-with v vp)
  view-path _
    = id

  view-inner-with
    : (v : ViewStack.View FormulaParentViewStack)
    → (vp : ViewStack.ViewPath FormulaParentViewStack v)
    → (v' : ViewStack.ViewInner FormulaParentViewStack v vp)
    → ViewStack.ViewInnerPath FormulaParentViewStack v vp v'
    → ViewStack.ViewInner FormulaViewStack
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ _ (_ , c) _
    = c

  view-inner-path
    : (v : ViewStack.View FormulaParentViewStack)
    → (vp : ViewStack.ViewPath FormulaParentViewStack v)
    → (v' : ViewStack.ViewInner FormulaParentViewStack v vp)
    → (vp' : ViewStack.ViewInnerPath FormulaParentViewStack v vp v')
    → ViewStack.ViewInnerPath FormulaViewStack
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ _ _
    = id

formula-view-stack-map
  : ViewStackMap
    FormulaParentViewStack
    FormulaViewStack
formula-view-stack-map
  = record {FormulaViewStackMap}

-- #### Event

module FormulaEventStackMap where

  mode
    : EventStack.Mode FormulaParentEventStack
    → EventStack.Mode FormulaEventStack
  mode
    = id

  mode-inner
    : EventStack.ModeInner FormulaParentEventStack
    → EventStack.ModeInner FormulaEventStack
  mode-inner _
    = tt

  event
    : (m : EventStack.Mode FormulaParentEventStack)
    → EventStack.Event FormulaEventStack (mode m)
    → EventStack.Event FormulaParentEventStack m
  event _ insert-parens
    = ι₁ insert-parens
  event _ insert-variable
    = ι₂ variable'
  event _ insert-symbol
    = ι₂ symbol

  event-inner
    : (m : EventStack.ModeInner FormulaParentEventStack)
    → EventStack.EventInner FormulaEventStack (mode-inner m)
    → EventStack.EventInner FormulaParentEventStack m
  event-inner _
    = id

formula-event-stack-map
  : EventStackMap
    FormulaParentEventStack
    FormulaEventStack
formula-event-stack-map
  = record {FormulaEventStackMap}

-- #### Editor

formula-simple-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleEditor
    FormulaViewStack
    FormulaEventStack
    (Any (SandboxState ss vs m))
formula-simple-editor ss vs m
  = simple-editor-map-view formula-view-stack-map
  $ simple-editor-map-event formula-event-stack-map
  $ formula-simple-parent-editor ss vs m

-- ### Split

formula-split-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SplitEditor
    FormulaViewStack
    FormulaEventStack
    (FormulaCategory ss vs m)
formula-split-editor ss vs m
  = split-editor-unit (SandboxState.split-function ss vs m)
  $ formula-simple-editor ss vs m

-- ### Partial

formula-partial-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → PartialEditor
    FormulaViewStack
    FormulaEventStack
    (Formula ss vs m)
formula-partial-editor ss vs m
  = split-editor-partial
  $ formula-split-editor ss vs m

