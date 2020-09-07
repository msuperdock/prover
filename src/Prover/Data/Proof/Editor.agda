module Prover.Data.Proof.Editor where

open import Prover.Client.Aeson
  using (Value)
open import Prover.Data.Formula
  using (Formula; _≟_frm)
open import Prover.Data.Formula.Editor
  using (FormulaEvent; decode-encode-formula; decode-formula; encode-formula;
  formula-split-editor)
open import Prover.Data.Identifier
  using (Identifier)
open import Prover.Data.Identifier.Editor
  using (decode-encode-identifier; decode-identifier; encode-identifier)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Number.Editor
  using (NumberEvent)
open import Prover.Data.Proof
  using (Branch; BranchPath; Proof; ProofPath; go; proof; stop)
open import Prover.Data.Proof.Editor.Meta
  using (ProofMetaFlatEventStack; ProofMetaFlatMode; proof-meta-flat-editor)
open import Prover.Data.Rule
  using (Rule; rule)
open import Prover.Data.Rules
  using (Rules; rul_∈_)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text.Editor
  using (TextEvent; TextFlatEventStack; command-flat-editor)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Editor
  using (EventStack; EventStackMap; MainEditor; SimpleEditor; SplitEditor;
    ViewStack; ViewStackMap)
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
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.View.Command
  using (Command; CommandFlatViewStack; CommandPath)
open import Prover.View.Line
  using (Line; line)
open import Prover.View.Text
  using (RichText)
open import Prover.View.Tree
  using (Tree; TreePath; draw-tree; draw-tree-with; go; stop)
open import Prover.View.Window
  using (Window; WindowFlatViewStack; WindowPath)
open import Prover.Prelude

open List'
  using ([]'; _∷'_)
open Vec
  using ([]; _∷_; _!_)

-- ## Types

-- ### View

data ProofViewInner
  : Set
  where

  window
    : Window
    → ProofViewInner

  command
    : Command
    → ProofViewInner

  both
    : Window
    → Command
    → ProofViewInner

data ProofViewInnerPath
  : ProofViewInner
  → Set
  where

  window
    : {w : Window}
    → WindowPath w
    → ProofViewInnerPath (window w)

  command
    : {c : Command}
    → CommandPath c
    → ProofViewInnerPath (command c)

  both
    : {w : Window}
    → {c : Command}
    → CommandPath c
    → ProofViewInnerPath (both w c)

ProofViewStack
  : ViewStack
ProofViewStack
  = record
  { View
    = List Line
  ; ViewPath
    = λ _ → ⊤
  ; ViewInner
    = λ _ _ → ProofViewInner
  ; ViewInnerPath
    = λ _ _ → ProofViewInnerPath
  }

-- ### Event

data ProofModeInner
  : Set
  where

  text
    : ProofModeInner

  number
    : ProofModeInner

  formula
    : ProofModeInner

data ProofEvent
  : Set
  where

  infer-hypotheses
    : ProofEvent

  substitute-meta
    : ProofEvent

ProofEventInner
  : ProofModeInner
  → Set
ProofEventInner text
  = TextEvent
ProofEventInner number
  = NumberEvent
ProofEventInner formula
  = FormulaEvent

ProofEventStack
  : EventStack
ProofEventStack
  = record
  { Mode
    = ⊤
  ; ModeInner
    = ProofModeInner
  ; Event
    = λ _ → ProofEvent
  ; EventInner
    = ProofEventInner
  }

-- ## Draw

-- ### Branch

module _
  {ss : Symbols}
  {rs : Rules ss}
  {vs : Variables}
  {a : ℕ}
  where

  draw-status
    : Vec (Formula ss vs false) a
    → Formula ss vs true
    → Bool
  draw-status hs f
    = Branch.is-complete-assumption hs f

  draw-formula
    : Formula ss vs true
    → RichText
  draw-formula
    = SplitEditor.draw-pure (formula-split-editor ss vs true)

  draw-branch
    : Vec (Formula ss vs false) a
    → Branch rs vs
    → Tree

  draw-branches
    : {n : ℕ}
    → Vec (Formula ss vs false) a
    → Vec (Branch rs vs) n
    → Vec Tree n

  draw-branch hs (Branch.assumption f)
    = Tree.leaf (line (draw-status hs f) (draw-formula f))
  draw-branch _ (Branch.rule _ _ [] c _)
    = Tree.leaf (line true (draw-formula c))
  draw-branch hs (Branch.rule _ _ bs@(_ ∷ _) c _)
    = Tree.node (draw-branches hs bs) (line true (draw-formula c))

  draw-branches _ []
    = []
  draw-branches hs (b ∷ bs)
    = draw-branch hs b ∷ draw-branches hs bs
  
  draw-path-branch
    : (hs : Vec (Formula ss vs false) a)
    → (b : Branch rs vs)
    → BranchPath b
    → TreePath (draw-branch hs b)

  draw-path-branches
    : {n : ℕ}
    → (hs : Vec (Formula ss vs false) a)
    → (bs : Vec (Branch rs vs) n)
    → (k : Fin n)
    → BranchPath (bs ! k)
    → TreePath (draw-branches hs bs ! k)

  draw-path-branch _ _ stop
    = stop
  draw-path-branch hs (Branch.rule _ _ bs@(_ ∷ _) _ _) (go k bp)
    = go k (draw-path-branches hs bs k bp)

  draw-path-branches hs (b ∷ _) zero bp
    = draw-path-branch hs b bp
  draw-path-branches hs (_ ∷ bs) (suc k) bp
    = draw-path-branches hs bs k bp

-- ### Proof

module _
  {ss : Symbols}
  {rs : Rules ss}
  {r : Rule ss}
  where

  draw-proof
    : Proof rs r
    → List Line
  draw-proof (proof b _)
    = draw-tree
      (draw-branch (Rule.hypotheses r) b)
  
  draw-proof-with
    : (p : Proof rs r)
    → ProofPath p
    → List Line
  draw-proof-with (proof b _) bp
    = draw-tree-with
      (draw-branch (Rule.hypotheses r) b)
      (draw-path-branch (Rule.hypotheses r) b bp)

-- ## Encode

-- ### Pattern

pattern tag-assumption
  = Value.string ('a' ∷' []')
pattern tag-rule
  = Value.string ('r' ∷' []')

-- ### Encode

encode-branch
  : {ss : Symbols}
  → {rs : Rules ss}
  → {vs : Variables}
  → Branch rs vs
  → Value

encode-branches
  : {ss : Symbols}
  → {rs : Rules ss}
  → {vs : Variables}
  → {n : ℕ}
  → Vec (Branch rs vs) n
  → List' Value

encode-branch (Branch.assumption c)
  = Value.array
  $ tag-assumption
  ∷' encode-formula c
  ∷' []'

encode-branch (Branch.rule (rule n _ _ _) _ bs c _)
  = Value.array
  $ tag-rule
  ∷' encode-identifier n
  ∷' Value.array (encode-branches bs)
  ∷' encode-formula c
  ∷' []'

encode-branches []
  = []'
encode-branches (b ∷ bs)
  = encode-branch b ∷' encode-branches bs

encode-proof
  : {ss : Symbols}
  → {rs : Rules ss}
  → {r : Rule ss}
  → Proof rs r
  → Value
encode-proof (proof b _)
  = encode-branch b

-- ### Decode

decode-branch
  : {ss : Symbols}
  → (rs : Rules ss)
  → (vs : Variables)
  → Value
  → Maybe (Branch rs vs)

decode-branches
  : {ss : Symbols}
  → (rs : Rules ss)
  → (vs : Variables)
  → List' Value
  → Maybe (List (Branch rs vs))

decode-branch {ss = ss} _ vs
  (Value.array (tag-assumption ∷' c ∷' []'))
  = Maybe.map Branch.assumption (decode-formula ss vs true c)

decode-branch {ss = ss} rs vs
  (Value.array (tag-rule ∷' n ∷' Value.array bs ∷' c ∷' []'))
  with decode-identifier n
  | decode-branches rs vs bs
  | decode-formula ss vs true c
... | nothing | _ | _
  = nothing
... | _ | nothing | _
  = nothing
... | _ | _ | nothing
  = nothing
... | just n' | just (any {a} bs') | just c'
  with Rules.lookup-member rs n'
... | nothing
  = nothing
... | just (Rules.member r p)
  with Rule.arity r ≟ a nat
... | no _
  = nothing
... | yes refl
  with Rule.match? r (Vec.map Branch.conclusion bs') c'
... | no _
  = nothing
... | yes m
  = just (Branch.rule r p bs' c' m)

decode-branch _ _ _
  = nothing

decode-branches _ _ []'
  = just (any [])
decode-branches rs vs (p ∷' ps)
  with decode-branch rs vs p
  | decode-branches rs vs ps
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just b | just (any bs)
  = just (any (b ∷ bs))

decode-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → Value
  → Maybe (Proof rs r)
decode-proof rs (rule _ vs _ c) v
  with decode-branch rs vs v
... | nothing
  = nothing
... | just b
  with Branch.conclusion b ≟ (Formula.to-meta-formula c) frm
... | no _
  = nothing
... | yes q
  = just (proof b q)

-- ### Valid

decode-encode-branch
  : {ss : Symbols}
  → {rs : Rules ss}
  → {vs : Variables}
  → (b : Branch rs vs)
  → decode-branch rs vs (encode-branch b) ≡ just b

decode-encode-branches
  : {ss : Symbols}
  → {rs : Rules ss}
  → {vs : Variables}
  → {n : ℕ}
  → (bs : Vec (Branch rs vs) n)
  → decode-branches rs vs (encode-branches bs) ≡ just (any bs)

decode-encode-branch {ss = ss} {vs = vs}
  (Branch.assumption c)
  with decode-formula ss vs true (encode-formula c)
  | decode-encode-formula c
... | _ | refl
  = refl

decode-encode-branch {ss = ss} {rs = rs} {vs = vs}
  (Branch.rule r@(rule n _ _ _) p bs c m)
  with decode-identifier (encode-identifier n)
  | decode-encode-identifier n
  | decode-branches rs vs (encode-branches bs)
  | decode-encode-branches bs
  | decode-formula ss vs true (encode-formula c)
  | decode-encode-formula c
... | _ | refl | _ | refl | _ | refl
  with Rules.lookup-member rs n
  | inspect (Rules.lookup-member rs) n
... | nothing | [ q ] 
  = ⊥-elim (Rules.lookup-member-nothing rs r q p)
... | just _ | [ q ]
  with Rules.lookup-member-just rs r p q
... | refl
  with Rule.arity r ≟ Rule.arity r nat
... | no ¬p
  = ⊥-elim (¬p refl)
... | yes refl
  with Rule.match? r (Vec.map Branch.conclusion bs) c
... | no ¬m
  = ⊥-elim (¬m m)
... | yes _
  = refl

decode-encode-branches []
  = refl
decode-encode-branches {rs = rs} {vs = vs} (b ∷ bs)
  with decode-branch rs vs (encode-branch b)
  | decode-encode-branch b
  | decode-branches rs vs (encode-branches bs)
  | decode-encode-branches bs
... | _ | refl | _ | refl
  = refl

decode-encode-proof
  : {ss : Symbols}
  → {rs : Rules ss}
  → {r : Rule ss}
  → (p : Proof rs r)
  → decode-proof rs r (encode-proof p) ≡ just p
decode-encode-proof {rs = rs} {r = r} (proof b q)
  with decode-branch rs (Rule.variables r) (encode-branch b)
  | decode-encode-branch b
... | _ | refl
  with Branch.conclusion b ≟ (Formula.to-meta-formula (Rule.conclusion r)) frm
... | no ¬q
  = ⊥-elim (¬q q)
... | yes _
  = refl

-- ### Split

proof-split-function
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SplitFunction Value (Proof rs r)
proof-split-function rs r
  = record
  { partial-function
    = decode-proof rs r
  ; function
    = encode-proof
  ; valid
    = decode-encode-proof
  }

-- ## Editors

-- ### Base

-- #### View

ProofBaseViewStack
  : BaseViewStack
ProofBaseViewStack
  = record
  { View
    = List Line
  ; ViewPath
    = λ _ → ⊤
  }

-- #### Event

ProofBaseEventStack
  : BaseEventStack
ProofBaseEventStack
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → ⊥
  }

-- #### Module

module ProofSimpleBaseEditor
  {ss : Symbols}
  (rs : Rules ss)
  (r : Rule ss)
  where

  -- ##### Types

  open BaseViewStack ProofBaseViewStack
  open BaseEventStack ProofBaseEventStack

  State
    : Set
  State
    = Proof rs r

  -- ##### State

  StatePath
    : State
    → Set
  StatePath
    = ProofPath

  initial
    : State
  initial
    = Proof.assumption

  initial-path
    : (s : State)
    → StatePath s
  initial-path _
    = stop

  initial-path-with
    : (s : State)
    → Direction
    → StatePath s
  initial-path-with p Direction.up
    = ProofPath.top p
  initial-path-with _ Direction.down
    = stop
  initial-path-with _ Direction.left
    = stop
  initial-path-with _ Direction.right
    = stop

  -- ##### Draw

  draw
    : State
    → View
  draw
    = draw-proof

  draw-with
    : (s : State)
    → StatePath s
    → View
  draw-with
    = draw-proof-with

  draw-path
    : (s : State)
    → (sp : StatePath s)
    → ViewPath (draw-with s sp)
  draw-path _ _
    = tt

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
  handle _ _ ()

  handle-direction
    : (s : State)
    → StatePath s
    → Direction
    → Maybe (StatePath s)
  handle-direction p pp Direction.up
    = ProofPath.up p pp
  handle-direction p pp Direction.down
    = ProofPath.down p pp
  handle-direction _ _ Direction.left
    = nothing
  handle-direction _ _ Direction.right
    = nothing

  handle-direction-valid
    : (s : State)
    → (d : Direction)
    → handle-direction s (initial-path-with s d) d ≡ nothing
  handle-direction-valid p Direction.up
    = ProofPath.up-top p
  handle-direction-valid _ Direction.down
    = refl
  handle-direction-valid _ Direction.left
    = refl
  handle-direction-valid _ Direction.right
    = refl

-- #### Editor

proof-simple-base-editor
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SimpleBaseEditor
    ProofBaseViewStack
    ProofBaseEventStack
    (Proof rs r)
proof-simple-base-editor rs r
  = record {ProofSimpleBaseEditor rs r}

-- ### Child

-- #### Key

data ProofKey
  : Set
  where

  infer
    : ProofKey

  meta
    : ProofKey

-- #### View

ProofChildViewStack
  : ProofKey
  → FlatViewStack
ProofChildViewStack infer
  = CommandFlatViewStack
ProofChildViewStack meta
  = WindowFlatViewStack

-- #### Event

ProofChildEventStack
  : ProofKey
  → FlatEventStack
ProofChildEventStack infer
  = TextFlatEventStack
ProofChildEventStack meta
  = ProofMetaFlatEventStack

-- #### Infer

module _
  {ss : Symbols}
  where

  module ProofSimpleChildEditorInfer
    (rs : Rules ss)
    (r : Rule ss)
    where
  
    BaseState
      : Set
    BaseState
      = Proof rs r

    open SimpleBaseEditor (proof-simple-base-editor rs r) using () renaming
      ( StatePath
        to BaseStatePath
      )

    record Result
      (p : Proof rs r)
      (pp : ProofPath p)
      : Set
      where
  
      constructor
      
        result
  
      field
  
        value
          : Rule ss
  
        member
          : rul value ∈ rs
  
        match
          : Formula.Match (Rule.conclusion value) (Proof.lookup p pp)

    result-map
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Identifier
      → Maybe (Result s sp)
    result-map p pp n
      with Rules.lookup-member rs n
    ... | nothing
      = nothing
    ... | just (Rules.member r q)
      with Formula.match? (Rule.conclusion r) (Proof.lookup p pp)
    ... | no _
      = nothing
    ... | yes m
      = just (result r q m)

    flat-editor
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → FlatEditor
        (ProofChildViewStack infer)
        (ProofChildEventStack infer)
        (Result s sp)
    flat-editor s sp
      = flat-editor-map (result-map s sp)
      $ command-flat-editor "i"

    update
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Result s sp
      → Σ BaseState BaseStatePath
    update p pp (result r q m)
      = Proof.infer p pp r q m

  proof-simple-child-editor-infer
    : (rs : Rules ss)
    → (r : Rule ss)
    → SimpleChildEditor
      (ProofChildViewStack infer)
      (ProofChildEventStack infer)
      (proof-simple-base-editor rs r)
  proof-simple-child-editor-infer rs r
    = record {ProofSimpleChildEditorInfer rs r}

-- #### Meta

module _
  {ss : Symbols}
  where

  module ProofSimpleChildEditorMeta
    (rs : Rules ss)
    (r : Rule ss)
    where

    BaseState
      : Set
    BaseState
      = Proof rs r

    open SimpleBaseEditor (proof-simple-base-editor rs r) using () renaming
      ( StatePath
        to BaseStatePath
      )

    Result
      : (s : BaseState)
      → BaseStatePath s
      → Set
    Result _ _
      = Meta × Formula ss (Rule.variables r) false

    flat-editor
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → FlatEditor
        (ProofChildViewStack meta)
        (ProofChildEventStack meta)
        (Result s sp)
    flat-editor _ _
      = proof-meta-flat-editor ss (Rule.variables r)

    update
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Result s sp
      → Σ BaseState BaseStatePath
    update p pp (m , f)
      = Proof.substitute-meta p pp m f

  proof-simple-child-editor-meta
    : (rs : Rules ss)
    → (r : Rule ss)
    → SimpleChildEditor
      (ProofChildViewStack meta)
      (ProofChildEventStack meta)
      (proof-simple-base-editor rs r)
  proof-simple-child-editor-meta rs r
    = record {ProofSimpleChildEditorMeta rs r}

-- #### Editor

proof-simple-child-editor
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → (k : ProofKey)
  → SimpleChildEditor
    (ProofChildViewStack k)
    (ProofChildEventStack k)
    (proof-simple-base-editor rs r)
proof-simple-child-editor rs r infer
  = proof-simple-child-editor-infer rs r
proof-simple-child-editor rs r meta
  = proof-simple-child-editor-meta rs r

-- ### Parent

-- #### View

ProofParentViewStack
  : ViewStack
ProofParentViewStack
  = view-stack-parent
    ProofBaseViewStack
    ProofChildViewStack

-- #### Event

ProofParentEventStack
  : EventStack
ProofParentEventStack
  = event-stack-parent
    ProofBaseEventStack
    ProofChildEventStack

-- #### Editor

proof-parent-editor
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SimpleEditor
    ProofParentViewStack
    ProofParentEventStack
    (Proof rs r)
proof-parent-editor rs r
  = simple-editor-parent
    ProofChildViewStack
    ProofChildEventStack
    (proof-simple-base-editor rs r)
    (proof-simple-child-editor rs r)

-- ### Simple

-- #### View

module ProofViewStackMap where

  view
    : ViewStack.View ProofParentViewStack
    → ViewStack.View ProofViewStack
  view
    = id

  view-with
    : (v : ViewStack.View ProofParentViewStack)
    → ViewStack.ViewPath ProofParentViewStack v
    → ViewStack.View ProofViewStack
  view-with v _
    = view v
  
  view-path
    : (v : ViewStack.View ProofParentViewStack)
    → (vp : ViewStack.ViewPath ProofParentViewStack v)
    → ViewStack.ViewPath ProofViewStack
      (view-with v vp)
  view-path _
    = id

  view-inner-with
    : (v : ViewStack.View ProofParentViewStack)
    → (vp : ViewStack.ViewPath ProofParentViewStack v)
    → (v' : ViewStack.ViewInner ProofParentViewStack v vp)
    → ViewStack.ViewInnerPath ProofParentViewStack v vp v'
    → ViewStack.ViewInner ProofViewStack
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ _ (infer , c) _
    = command c
  view-inner-with _ _ (meta , (w , nothing)) _
    = window w
  view-inner-with _ _ (meta , (w , just (_ , c))) _
    = both w c

  view-inner-path
    : (v : ViewStack.View ProofParentViewStack)
    → (vp : ViewStack.ViewPath ProofParentViewStack v)
    → (v' : ViewStack.ViewInner ProofParentViewStack v vp)
    → (vp' : ViewStack.ViewInnerPath ProofParentViewStack v vp v')
    → ViewStack.ViewInnerPath ProofViewStack
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ _ (infer , _) cp
    = command cp
  view-inner-path _ _ (meta , (_ , nothing)) wp
    = window wp
  view-inner-path _ _ (meta , (_ , just _)) cp
    = both cp

proof-view-stack-map
  : ViewStackMap
    ProofParentViewStack
    ProofViewStack
proof-view-stack-map
  = record {ProofViewStackMap}

-- #### Event

module ProofEventStackMap where

  mode
    : EventStack.Mode ProofParentEventStack
    → EventStack.Mode ProofEventStack
  mode
    = id

  mode-inner
    : EventStack.ModeInner ProofParentEventStack
    → EventStack.ModeInner ProofEventStack
  mode-inner (infer , _)
    = text
  mode-inner (meta , ProofMetaFlatMode.text)
    = text
  mode-inner (meta , ProofMetaFlatMode.number)
    = number
  mode-inner (meta , ProofMetaFlatMode.formula)
    = formula

  event
    : (m : EventStack.Mode ProofParentEventStack)
    → EventStack.Event ProofEventStack (mode m)
    → EventStack.Event ProofParentEventStack m
  event _ infer-hypotheses
    = ι₂ infer
  event _ substitute-meta
    = ι₂ meta

  event-inner
    : (m : EventStack.ModeInner ProofParentEventStack)
    → EventStack.EventInner ProofEventStack (mode-inner m)
    → EventStack.EventInner ProofParentEventStack m
  event-inner (infer , _)
    = id
  event-inner (meta , ProofMetaFlatMode.text)
    = id
  event-inner (meta , ProofMetaFlatMode.number)
    = id
  event-inner (meta , ProofMetaFlatMode.formula)
    = id

proof-event-stack-map
  : EventStackMap
    ProofParentEventStack
    ProofEventStack
proof-event-stack-map
  = record {ProofEventStackMap}

-- #### Editor

proof-simple-editor
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SimpleEditor
    ProofViewStack
    ProofEventStack
    (Proof rs r)
proof-simple-editor rs r
  = simple-editor-map-view proof-view-stack-map
  $ simple-editor-map-event proof-event-stack-map
  $ proof-parent-editor rs r

-- ### Main

proof-main-editor
  : {ss : Symbols}
  → Rules ss
  → Rule ss
  → MainEditor
    ProofViewStack
    ProofEventStack
    Value
proof-main-editor rs r
  = record
  { simple-editor
    = proof-simple-editor rs r
  ; split-function
    = proof-split-function rs r
  ; bool-function
    = Proof.is-complete
  }

