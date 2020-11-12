module Prover.Data.Formula.Editor where

open import Prover.Client.Aeson
  using (Value)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Formula.State
  using (FormulaState; FormulaStatePath; Left; Right; SandboxState;
    SandboxStatePath; center; end; go; left; nothing; right; stop)
open import Prover.Data.Formula.Insert
  using (sandbox-state-insert-parens; sandbox-state-insert-symbol;
    sandbox-state-insert-variable)
open import Prover.Data.Identifier.Editor
  using (decode-encode-identifier; decode-identifier; encode-identifier)
open import Prover.Data.Meta.Editor
  using (draw-meta)
open import Prover.Data.Symbol
  using (Symbol; symbol)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text.Editor
  using (TextEvent; TextFlatEventStack; command-flat-editor)
open import Prover.Data.Token
  using (Token)
open import Prover.Data.Variables
  using (Variables; var_∈?_)
open import Prover.Editor
  using (EventStack; EventStackMap; SimpleEditor; SimplePartialEditor;
    SimpleSplitEditor; ViewStack; ViewStackMap)
open import Prover.Editor.Base
  using (BaseEventStack; BaseViewStack; SimpleBaseEditor)
open import Prover.Editor.Child
  using (SimpleChildEditor)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatViewStack)
open import Prover.Editor.Map
  using (flat-editor-map)
open import Prover.Editor.Map.Event
  using (simple-editor-map-event)
open import Prover.Editor.Map.View
  using (simple-editor-map-view)
open import Prover.Editor.Parent
  using (event-stack-parent; simple-editor-parent; view-stack-parent)
open import Prover.View.Command
  using (Command; CommandFlatViewStack; CommandPath)
open import Prover.View.Text
  using (RichText; RichTextPath; plain; style; text)
open import Prover.Prelude

open List'
  using ([]'; _∷'_)
open Vec
  using ([]; _∷_; _!_)

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
    : {s : Symbol}
    → Left ss vs m s
    → RichText

  draw-formula-right
    : {s : Symbol}
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
    = RichText.plain (String.to-list "_")
  draw-formula (FormulaState.parens s)
    = RichText.wrap "(" ")" (draw-sandbox s)
  draw-formula (FormulaState.meta m)
    = draw-meta (String.to-list (Nat.show m))
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
    = RichText.plain (Token.characters t)
  draw-formula-center (t ∷ ts@(_ ∷ _)) (s ∷ ss)
    = RichText.texts
    $ RichText.plain (Token.characters t)
    ∷ draw-sandbox s
    ∷ draw-formula-center ts ss
    ∷ []

  draw-sandbox (any (SandboxState.singleton f))
    = draw-formula f
  draw-sandbox (any (SandboxState.cons f _ s _))
    = RichText.texts
    $ draw-formula f
    ∷ RichText.plain (String.to-list "   ")
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
  draw-path-sandbox-go (any (SandboxState.cons _ _ s _)) (suc k) fp
    = text (suc (suc zero)) (draw-path-sandbox-go s k fp)

-- ## Encoding

-- ### Pattern

pattern tag-meta
  = Value.string ('m' ∷' []')
pattern tag-variable
  = Value.string ('v' ∷' []')
pattern tag-symbol
  = Value.string ('s' ∷' []')

-- ### Encode

encode-formula
  : {ss : Symbols}
  → {vs : Variables}
  → {m : Bool}
  → Formula ss vs m
  → Value

encode-formulas
  : {ss : Symbols}
  → {vs : Variables}
  → {m : Bool}
  → {n : ℕ}
  → Vec (Formula ss vs m) n
  → List' Value

encode-formula (Formula.meta m)
  = Value.array
  $ tag-meta
  ∷' Value.number m
  ∷' []'

encode-formula (Formula.variable' v _)
  = Value.array 
  $ tag-variable
  ∷' encode-identifier v
  ∷' []'

encode-formula (Formula.symbol (symbol _ n _ _ _) _ fs)
  = Value.array
  $ tag-symbol
  ∷' encode-identifier n
  ∷' Value.array (encode-formulas fs)
  ∷' []'

encode-formulas []
  = []'
encode-formulas (f ∷ fs)
  = encode-formula f ∷' encode-formulas fs

-- ### Decode

decode-formula
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → Value
  → Maybe (Formula ss vs m)

decode-formulas
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → List' Value
  → Maybe (List (Formula ss vs m))

decode-formula _ vs _
  (Value.array (tag-variable ∷' n ∷' []'))
  with decode-identifier n
... | nothing
  = nothing
... | just v
  with var v ∈? vs
... | no _
  = nothing
... | yes p
  = just (Formula.variable' v p)

decode-formula ss vs m
  (Value.array (tag-symbol ∷' n ∷' Value.array fs ∷' []'))
  with decode-identifier n
  | decode-formulas ss vs m fs
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just n' | just (any {a} fs')
  with Symbols.lookup-member ss n'
... | nothing
  = nothing
... | just (Symbols.member s p)
  with Symbol.arity s ≟ a nat
... | no _
  = nothing
... | yes refl
  = just (Formula.symbol s p fs')

decode-formula _ _ true
  (Value.array (tag-meta ∷' Value.number n ∷' []'))
  = just (Formula.meta n)

decode-formula _ _ _ _
  = nothing

decode-formulas _ _ _ []'
  = just (any [])
decode-formulas ss vs m (f ∷' fs)
  with decode-formula ss vs m f
  | decode-formulas ss vs m fs
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just f' | just (any fs')
  = just (any (f' ∷ fs'))

-- ### Valid

decode-encode-formula
  : {ss : Symbols}
  → {vs : Variables}
  → {m : Bool}
  → (f : Formula ss vs m)
  → decode-formula ss vs m (encode-formula f) ≡ just f

decode-encode-formulas
  : {ss : Symbols}
  → {vs : Variables}
  → {m : Bool}
  → {n : ℕ}
  → (fs : Vec (Formula ss vs m) n)
  → decode-formulas ss vs m (encode-formulas fs) ≡ just (any fs)

decode-encode-formula
  (Formula.meta _)
  = refl

decode-encode-formula {vs = vs}
  (Formula.variable' v p)
  with decode-identifier (encode-identifier v)
  | decode-encode-identifier v
... | _ | refl
  with var v ∈? vs
... | no ¬p
  = ⊥-elim (¬p p)
... | yes _
  = refl

decode-encode-formula {ss = ss} {vs = vs} {m = m}
  (Formula.symbol s@(symbol _ n _ _ _) p fs)
  with decode-identifier (encode-identifier n)
  | decode-encode-identifier n
  | decode-formulas ss vs m (encode-formulas fs)
  | decode-encode-formulas fs
... | _ | refl | _ | refl
  with Symbols.lookup-member ss n
  | inspect (Symbols.lookup-member ss) n
... | nothing | [ q ]
  = ⊥-elim (Symbols.lookup-member-nothing ss s q p)
... | just _ | [ q ]
  with Symbols.lookup-member-just ss s p q
... | refl
  with Symbol.arity s ≟ Symbol.arity s nat
... | no ¬p
  = ⊥-elim (¬p refl)
... | yes refl
  = refl

decode-encode-formulas []
  = refl
decode-encode-formulas {ss = ss} {vs = vs} {m = m} (f ∷ fs)
  with decode-formula ss vs m (encode-formula f)
  | decode-encode-formula f
  | decode-formulas ss vs m (encode-formulas fs)
  | decode-encode-formulas fs
... | _ | refl | _ | refl
  = refl

-- ## Editors

-- ### SimpleBaseEditor

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
    → StatePath s
  initial-path _
    = end

  initial-path-with
    : (s : State)
    → Direction
    → StatePath s
  initial-path-with s Direction.up
    = SandboxStatePath.leftmost s
  initial-path-with s Direction.down
    = SandboxStatePath.leftmost s
  initial-path-with s Direction.left
    = SandboxStatePath.leftmost s
  initial-path-with _ Direction.right
    = end

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
    → handle-direction s (initial-path-with s d) d ≡ nothing
  handle-direction-valid _ Direction.up
    = refl
  handle-direction-valid _ Direction.down
    = refl
  handle-direction-valid s Direction.left
    = SandboxStatePath.left-leftmost s
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

-- ### SimpleChildEditor

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
    = flat-editor-map (Variables.find-member vs)
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

-- ### SimpleEditor

-- #### Parent

FormulaParentViewStack
  : ViewStack
FormulaParentViewStack
  = view-stack-parent
    FormulaBaseViewStack
    FormulaChildViewStack

FormulaParentEventStack
  : EventStack
FormulaParentEventStack
  = event-stack-parent
    FormulaBaseEventStack
    FormulaChildEventStack

formula-parent-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleEditor
    FormulaParentViewStack
    FormulaParentEventStack
    (Any (SandboxState ss vs m))
formula-parent-editor ss vs m
  = simple-editor-parent
    FormulaChildViewStack
    FormulaChildEventStack
    (formula-simple-base-editor ss vs m)
    (formula-simple-child-editor ss vs m)

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
  $ formula-parent-editor ss vs m

-- ### SimpleSplitEditor

formula-simple-split-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimpleSplitEditor
    FormulaViewStack
    FormulaEventStack
    (Formula ss vs m)
formula-simple-split-editor ss vs m
  = record
  { editor
    = formula-simple-editor ss vs m
  ; split-functor
    = SandboxState.split-function ss vs m
  }

-- ### SimplePartialEditor

formula-simple-partial-editor
  : (ss : Symbols)
  → (vs : Variables)
  → (m : Bool)
  → SimplePartialEditor
    FormulaViewStack
    FormulaEventStack
    (Formula ss vs m)
formula-simple-partial-editor ss vs m
  = SimpleSplitEditor.partial-editor (formula-simple-split-editor ss vs m)

