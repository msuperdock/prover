module Prover.Data.Proof.Editor where

open import Prover.Category.Encoding
  using (Encoding)
open import Prover.Client.Aeson
  using (Value)
open import Prover.Data.Formula
  using (Formula; _≟_frm)
open import Prover.Data.Formula.Editor
  using (FormulaEvent; decode-encode-formula; decode-formula; encode-formula;
    simple-split-editor-formula)
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
  using (ProofMetaFlatMode; flat-editor-proof-meta; flat-event-stack-proof-meta)
open import Prover.Data.Rule
  using (Rule; rule)
open import Prover.Data.Rules
  using (Rules; rul_∈_)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text.Editor
  using (TextEvent; flat-editor-command; flat-event-stack-text)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Editor
  using (EventStack; EventStackMap; SimpleEditor; SimpleMainEditor;
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

view-stack-proof
  : ViewStack
view-stack-proof
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

event-stack-proof
  : EventStack
event-stack-proof
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
  where

  draw-status
    : List (Formula ss vs false)
    → Formula ss vs true
    → Bool
  draw-status hs f
    = Branch.is-complete-assumption hs f

  draw-formula
    : Formula ss vs true
    → RichText
  draw-formula
    = SimpleSplitEditor.draw-pure (simple-split-editor-formula ss vs true)

  draw-branch
    : List (Formula ss vs false)
    → Branch rs vs
    → Tree

  draw-branches
    : {n : ℕ}
    → List (Formula ss vs false)
    → Vec (Branch rs vs) n
    → Vec Tree n

  draw-branch hs (Branch.assumption f)
    = Tree.leaf (line (draw-status hs f) (draw-formula f))
  draw-branch _ (Branch.rule _ _ [] c _)
    = Tree.leaf (line true (draw-formula c))
  draw-branch hs (Branch.rule _ _ bs@(_ ∷ _) c _)
    = Tree.node (any (draw-branches hs bs)) (line true (draw-formula c))

  draw-branches _ []
    = []
  draw-branches hs (b ∷ bs)
    = draw-branch hs b ∷ draw-branches hs bs
  
  draw-path-branch
    : (hs : List (Formula ss vs false))
    → (b : Branch rs vs)
    → BranchPath b
    → TreePath (draw-branch hs b)

  draw-path-branches
    : {n : ℕ}
    → (hs : List (Formula ss vs false))
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

-- ## Encoding

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

-- ### Record

encoding-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → Encoding (Proof rs r) Value
encoding-proof rs r
  = record
  { encode
    = encode-proof
  ; decode
    = decode-proof rs r
  ; decode-encode
    = decode-encode-proof
  }

-- ## Editors

-- ### SimpleBaseEditor

-- #### View

base-view-stack-proof
  : BaseViewStack
base-view-stack-proof
  = record
  { View
    = List Line
  ; ViewPath
    = λ _ → ⊤
  }

-- #### Event

base-event-stack-proof
  : BaseEventStack
base-event-stack-proof
  = record
  { Mode
    = ⊤
  ; Event
    = λ _ → ⊥
  }

-- #### Module

module SimpleBaseEditorProof
  {ss : Symbols}
  (rs : Rules ss)
  (r : Rule ss)
  where

  -- ##### Types

  open BaseViewStack base-view-stack-proof
  open BaseEventStack base-event-stack-proof

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

simple-base-editor-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SimpleBaseEditor
    base-view-stack-proof
    base-event-stack-proof
    (Proof rs r)
simple-base-editor-proof rs r
  = record {SimpleBaseEditorProof rs r}

-- ### SimpleChildEditor

-- #### Key

data ProofKey
  : Set
  where

  infer
    : ProofKey

  meta
    : ProofKey

-- #### View

flat-view-stack-proof-child
  : ProofKey
  → FlatViewStack
flat-view-stack-proof-child infer
  = CommandFlatViewStack
flat-view-stack-proof-child meta
  = WindowFlatViewStack

-- #### Event

flat-event-stack-proof-child
  : ProofKey
  → FlatEventStack
flat-event-stack-proof-child infer
  = flat-event-stack-text
flat-event-stack-proof-child meta
  = flat-event-stack-proof-meta

-- #### Infer

module _
  {ss : Symbols}
  where

  module SimpleChildEditorProofInfer
    (rs : Rules ss)
    (r : Rule ss)
    where
  
    BaseState
      : Set
    BaseState
      = Proof rs r

    open SimpleBaseEditor (simple-base-editor-proof rs r) using () renaming
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
  
        .member
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
        (flat-view-stack-proof-child infer)
        (flat-event-stack-proof-child infer)
        (Result s sp)
    flat-editor s sp
      = flat-editor-map (result-map s sp)
      $ flat-editor-command "i"

    update
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Result s sp
      → Σ BaseState BaseStatePath
    update p pp (result r q m)
      = Proof.infer p pp r q m

  simple-child-editor-proof-infer
    : (rs : Rules ss)
    → (r : Rule ss)
    → SimpleChildEditor
      (flat-view-stack-proof-child infer)
      (flat-event-stack-proof-child infer)
      (simple-base-editor-proof rs r)
  simple-child-editor-proof-infer rs r
    = record {SimpleChildEditorProofInfer rs r}

-- #### Meta

module _
  {ss : Symbols}
  where

  module SimpleChildEditorProofMeta
    (rs : Rules ss)
    (r : Rule ss)
    where

    BaseState
      : Set
    BaseState
      = Proof rs r

    open SimpleBaseEditor (simple-base-editor-proof rs r) using () renaming
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
        (flat-view-stack-proof-child meta)
        (flat-event-stack-proof-child meta)
        (Result s sp)
    flat-editor _ _
      = flat-editor-proof-meta ss (Rule.variables r)

    update
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Result s sp
      → Σ BaseState BaseStatePath
    update p pp (m , f)
      = Proof.substitute-meta p pp m f

  simple-child-editor-proof-meta
    : (rs : Rules ss)
    → (r : Rule ss)
    → SimpleChildEditor
      (flat-view-stack-proof-child meta)
      (flat-event-stack-proof-child meta)
      (simple-base-editor-proof rs r)
  simple-child-editor-proof-meta rs r
    = record {SimpleChildEditorProofMeta rs r}

-- #### Editor

simple-child-editor-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → (k : ProofKey)
  → SimpleChildEditor
    (flat-view-stack-proof-child k)
    (flat-event-stack-proof-child k)
    (simple-base-editor-proof rs r)
simple-child-editor-proof rs r infer
  = simple-child-editor-proof-infer rs r
simple-child-editor-proof rs r meta
  = simple-child-editor-proof-meta rs r

-- ### SimpleEditor

-- #### Parent

view-stack-proof-parent
  : ViewStack
view-stack-proof-parent
  = view-stack-parent
    base-view-stack-proof
    flat-view-stack-proof-child

event-stack-proof-parent
  : EventStack
event-stack-proof-parent
  = event-stack-parent
    base-event-stack-proof
    flat-event-stack-proof-child

simple-editor-proof-parent
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SimpleEditor
    view-stack-proof-parent
    event-stack-proof-parent
    (Proof rs r)
simple-editor-proof-parent rs r
  = simple-editor-parent
    flat-view-stack-proof-child
    flat-event-stack-proof-child
    (simple-base-editor-proof rs r)
    (simple-child-editor-proof rs r)

-- #### View

module ViewStackMapProof where

  view
    : ViewStack.View view-stack-proof-parent
    → ViewStack.View view-stack-proof
  view
    = id

  view-with
    : (v : ViewStack.View view-stack-proof-parent)
    → ViewStack.ViewPath view-stack-proof-parent v
    → ViewStack.View view-stack-proof
  view-with v _
    = view v
  
  view-path
    : (v : ViewStack.View view-stack-proof-parent)
    → (vp : ViewStack.ViewPath view-stack-proof-parent v)
    → ViewStack.ViewPath view-stack-proof
      (view-with v vp)
  view-path _
    = id

  view-inner-with
    : (v : ViewStack.View view-stack-proof-parent)
    → (vp : ViewStack.ViewPath view-stack-proof-parent v)
    → (v' : ViewStack.ViewInner view-stack-proof-parent v vp)
    → ViewStack.ViewInnerPath view-stack-proof-parent v vp v'
    → ViewStack.ViewInner view-stack-proof
      (view-with v vp)
      (view-path v vp)
  view-inner-with _ _ (infer , c) _
    = command c
  view-inner-with _ _ (meta , (w , nothing)) _
    = window w
  view-inner-with _ _ (meta , (w , just (_ , c))) _
    = both w c

  view-inner-path
    : (v : ViewStack.View view-stack-proof-parent)
    → (vp : ViewStack.ViewPath view-stack-proof-parent v)
    → (v' : ViewStack.ViewInner view-stack-proof-parent v vp)
    → (vp' : ViewStack.ViewInnerPath view-stack-proof-parent v vp v')
    → ViewStack.ViewInnerPath view-stack-proof
      (view-with v vp)
      (view-path v vp)
      (view-inner-with v vp v' vp')
  view-inner-path _ _ (infer , _) cp
    = command cp
  view-inner-path _ _ (meta , (_ , nothing)) wp
    = window wp
  view-inner-path _ _ (meta , (_ , just _)) cp
    = both cp

view-stack-map-proof
  : ViewStackMap
    view-stack-proof-parent
    view-stack-proof
view-stack-map-proof
  = record {ViewStackMapProof}

-- #### Event

module EventStackMapProof where

  mode
    : EventStack.Mode event-stack-proof-parent
    → EventStack.Mode event-stack-proof
  mode
    = id

  mode-inner
    : EventStack.ModeInner event-stack-proof-parent
    → EventStack.ModeInner event-stack-proof
  mode-inner (infer , _)
    = text
  mode-inner (meta , ProofMetaFlatMode.text)
    = text
  mode-inner (meta , ProofMetaFlatMode.number)
    = number
  mode-inner (meta , ProofMetaFlatMode.formula)
    = formula

  event
    : (m : EventStack.Mode event-stack-proof-parent)
    → EventStack.Event event-stack-proof (mode m)
    → EventStack.Event event-stack-proof-parent m
  event _ infer-hypotheses
    = ι₂ infer
  event _ substitute-meta
    = ι₂ meta

  event-inner
    : (m : EventStack.ModeInner event-stack-proof-parent)
    → EventStack.EventInner event-stack-proof (mode-inner m)
    → EventStack.EventInner event-stack-proof-parent m
  event-inner (infer , _)
    = id
  event-inner (meta , ProofMetaFlatMode.text)
    = id
  event-inner (meta , ProofMetaFlatMode.number)
    = id
  event-inner (meta , ProofMetaFlatMode.formula)
    = id

event-stack-map-proof
  : EventStackMap
    event-stack-proof-parent
    event-stack-proof
event-stack-map-proof
  = record {EventStackMapProof}

-- #### Editor

simple-editor-proof
  : {ss : Symbols}
  → (rs : Rules ss)
  → (r : Rule ss)
  → SimpleEditor
    view-stack-proof
    event-stack-proof
    (Proof rs r)
simple-editor-proof rs r
  = simple-editor-map-view view-stack-map-proof
  $ simple-editor-map-event event-stack-map-proof
  $ simple-editor-proof-parent rs r

-- ### SimpleMainEditor

simple-main-editor-proof
  : {ss : Symbols}
  → Rules ss
  → Rule ss
  → SimpleMainEditor
    view-stack-proof
    event-stack-proof
    Value
simple-main-editor-proof rs r
  = record
  { editor
    = simple-editor-proof rs r
  ; state-encoding
    = encoding-proof rs r
  ; bool-function
    = Proof.is-complete
  }

