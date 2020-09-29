module Prover.Editor where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; nil)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Bool
  using (DependentBoolFunction)
open import Prover.Category.Dependent.Encoding
  using (DependentEncoding)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; dependent-simple-category-set)
open import Prover.Category.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Category.Dependent.Simple.Convert
  using (dependent-category-simple)
open import Prover.Category.Dependent.Simple.Encoding
  using (DependentSimpleEncoding)
open import Prover.Category.Dependent.Simple.Encoding.Convert
  using (dependent-encoding-simple)
open import Prover.Category.Dependent.Simple.Partial
  using (DependentSimplePartialFunction; dependent-simple-partial-function-bool)
open import Prover.Category.Dependent.Simple.Split
  using (DependentSimpleSplitFunctor; dependent-simple-split-functor-bool;
    dependent-simple-split-functor-partial)
open import Prover.Category.Dependent.Simple.Split.Convert
  using (dependent-split-functor-simple)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; dependent-split-functor-bool)
open import Prover.Category.Encoding
  using (Encoding)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Prelude

-- ## Stacks

-- ### ViewStack

record ViewStack
  : Set₁
  where

  field

    View
      : Set

    ViewPath
      : View
      → Set
    
    ViewInner
      : (v : View)
      → ViewPath v
      → Set

    ViewInnerPath
      : (v : View)
      → (vp : ViewPath v)
      → ViewInner v vp
      → Set

-- ### EventStack

record EventStack
  : Set₁
  where

  field

    Mode
      : Set

    ModeInner
      : Set

    Event
      : Mode
      → Set

    EventInner
      : ModeInner
      → Set

-- ## StackMaps

-- ### ViewStackMap

-- #### Definition

record ViewStackMap
  (V W : ViewStack)
  : Set
  where

  field

    view
      : ViewStack.View V
      → ViewStack.View W

    view-with
      : (v : ViewStack.View V)
      → ViewStack.ViewPath V v
      → ViewStack.View W
    
    view-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → ViewStack.ViewPath W
        (view-with v vp)

    view-inner-with
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → ViewStack.ViewInnerPath V v vp v'
      → ViewStack.ViewInner W
        (view-with v vp)
        (view-path v vp)

    view-inner-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → (vp' : ViewStack.ViewInnerPath V v vp v')
      → ViewStack.ViewInnerPath W
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')

-- #### Compose

module _
  {V W X : ViewStack}
  where

  module ViewStackMapComposeWith
    (F : ViewStack.View V → ViewStackMap W X)
    (G : ViewStackMap V W)
    where

    view
      : ViewStack.View V
      → ViewStack.View X
    view v
      = ViewStackMap.view (F v)
        (ViewStackMap.view G v)

    view-with
      : (v : ViewStack.View V)
      → ViewStack.ViewPath V v
      → ViewStack.View X
    view-with v vp
      = ViewStackMap.view-with (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)
    
    view-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → ViewStack.ViewPath X
        (view-with v vp)
    view-path v vp
      = ViewStackMap.view-path (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)

    view-inner-with
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → ViewStack.ViewInnerPath V v vp v'
      → ViewStack.ViewInner X
        (view-with v vp)
        (view-path v vp)
    view-inner-with v vp v' vp'
      = ViewStackMap.view-inner-with (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)
        (ViewStackMap.view-inner-with G v vp v' vp')
        (ViewStackMap.view-inner-path G v vp v' vp')

    view-inner-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → (vp' : ViewStack.ViewInnerPath V v vp v')
      → ViewStack.ViewInnerPath X
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')
    view-inner-path v vp v' vp'
      = ViewStackMap.view-inner-path (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)
        (ViewStackMap.view-inner-with G v vp v' vp')
        (ViewStackMap.view-inner-path G v vp v' vp')

  view-stack-map-compose-with
    : (ViewStack.View V → ViewStackMap W X)
    → ViewStackMap V W
    → ViewStackMap V X
  view-stack-map-compose-with F G
    = record {ViewStackMapComposeWith F G}

-- ### EventStackMap

record EventStackMap
  (E F : EventStack)
  : Set
  where

  field

    mode
      : EventStack.Mode E
      → EventStack.Mode F

    mode-inner
      : EventStack.ModeInner E
      → EventStack.ModeInner F

    event
      : (m : EventStack.Mode E)
      → EventStack.Event F (mode m)
      → EventStack.Event E m

    event-inner
      : (m : EventStack.ModeInner E)
      → EventStack.EventInner F (mode-inner m)
      → EventStack.EventInner E m

-- ## Editors (basic)

-- ### Editor

record Editor
  (V : ViewStack)
  (E : EventStack)
  (C : Category)
  : Set₁
  where
 
  -- #### Types

  open EventStack E

  open Category C using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    )

  -- #### State

  field

    StatePath
      : State
      → Set

    StateInner
      : (s : State)
      → StatePath s
      → Set

    StateInnerPath
      : (s : State)
      → (sp : StatePath s)
      → StateInner s sp
      → Set

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

  field

    initial
      : State

    initial-path
      : (s : State)
      → StatePath s

  initial-path'
    : StatePath initial
  initial-path'
    = initial-path initial

  field

    -- The initial path when entering from the given direction.
    initial-path-with
      : (s : State)
      → Direction
      → StatePath s

  -- #### Draw

  field

    draw-stack
      : ViewStackMap StateStack V

  open ViewStackMap draw-stack public using () renaming
    ( view
      to draw
    ; view-with
      to draw-with
    ; view-path
      to draw-path
    ; view-inner-with
      to draw-inner-with
    ; view-inner-path
      to draw-inner-path
    )

  -- #### Mode

  field

    mode
      : (s : State)
      → StatePath s
      → Mode

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner

  -- #### Handle

  field

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)

    handle-direction-valid
      : (s : State)
      → (d : Direction)
      → handle-direction s (initial-path-with s d) d ≡ nothing

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'

-- ### SimpleEditor

data SimpleEditor
  (V : ViewStack)
  (E : EventStack)
  : Set
  → Set₁
  where

  any
    : {C : Category}
    → Editor V E C
    → SimpleEditor V E (Category.Object C)

simple-editor-draw
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → SimpleEditor V E A
  → A
  → ViewStack.View V
simple-editor-draw (any e)
  = Editor.draw e

-- ## Editors (dependent)

-- ### DependentEditor

-- #### Types

DependentEditor
  : {n : ℕ}
  → ViewStack
  → EventStack
  → {C : ChainCategory n}
  → DependentCategory C
  → Set₁

record DependentEditor'
  {n : ℕ}
  (V : ViewStack)
  (E : EventStack)
  {C : ChainCategory (suc n)}
  (C' : DependentCategory C)
  : Set₁

-- #### Definitions

DependentEditor {n = zero} V E
  = Editor V E
DependentEditor {n = suc _} V E
  = DependentEditor' V E

record DependentEditor' V E {C} C' where

  inductive

  field

    editor
      : (x : ChainCategory.Object C)
      → DependentEditor V E
        (DependentCategory.category C' x)

module DependentEditor
  = DependentEditor'

-- ### DependentSplitEditor

record DependentSplitEditor
  {n : ℕ}
  (V : ViewStack)
  (E : EventStack)
  {C : ChainCategory n}
  (C' : DependentCategory C)
  : Set₁
  where

  field

    {StateCategory}
      : DependentCategory C

    editor
      : DependentEditor V E StateCategory

    split-functor
      : DependentSplitFunctor StateCategory C'

  bool-function
    : DependentBoolFunction StateCategory
  bool-function
    = dependent-split-functor-bool split-functor

dependent-split-editor-tail
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory (suc n)}
  → {C' : DependentCategory C}
  → DependentSplitEditor V E C'
  → (x : ChainCategory.Object C)
  → DependentSplitEditor V E
    (DependentCategory.category C' x)
dependent-split-editor-tail e x
  = record
  { editor
    = DependentEditor.editor
      (DependentSplitEditor.editor e) x
  ; split-functor
    = DependentSplitFunctor.split-functor
      (DependentSplitEditor.split-functor e) x
  }

-- ### DependentInnerEditor

record DependentInnerEditor
  {n : ℕ}
  (V : ViewStack)
  (E : EventStack)
  (S P : Set)
  {C : ChainCategory n}
  (C' : DependentCategory C)
  : Set₁
  where

  field

    {StateCategory}
      : DependentCategory C

    editor
      : DependentEditor V E StateCategory

    state-encoding
      : DependentEncoding StateCategory S

    pure-encoding
      : DependentEncoding C' P

    split-functor
      : DependentSplitFunctor StateCategory C'
  
  split-editor
    : DependentSplitEditor V E C'
  split-editor
    = record
    { editor
      = editor
    ; split-functor
      = split-functor
    }

  bool-function
    : DependentBoolFunction StateCategory
  bool-function
    = dependent-split-functor-bool split-functor

-- ### DependentSimpleEditor

-- #### Types

DependentSimpleEditor
  : {n : ℕ}
  → ViewStack
  → EventStack
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → Set₁

record DependentSimpleEditor'
  {n : ℕ}
  (V : ViewStack)
  (E : EventStack)
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleCategory C)
  : Set₁

-- #### Definitions

DependentSimpleEditor {n = zero} V E
  = SimpleEditor V E
DependentSimpleEditor {n = suc _} V E
  = DependentSimpleEditor' V E

record DependentSimpleEditor' V E {C} C' where

  inductive

  field

    editor
      : (x : ChainCategory.Object C)
      → DependentSimpleEditor V E
        (DependentSimpleCategory.category C' x)

module DependentSimpleEditor
  = DependentSimpleEditor'

-- #### Conversion

dependent-editor-simple
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentEditor V E C'
  → DependentSimpleEditor V E
    (dependent-category-simple C')

dependent-editor-simple {n = zero} e
  = any e

dependent-editor-simple {n = suc _} e
  = record
  { editor
    = λ x → dependent-editor-simple
      (DependentEditor.editor e x)
  }

-- ### DependentSimplePartialEditor

record DependentSimplePartialEditor
  {n : ℕ}
  (V : ViewStack)
  (E : EventStack)
  {C : ChainCategory n}
  (C' : DependentSet C)
  : Set₁
  where

  field
  
    {StateCategory}
      : DependentSimpleCategory C

    editor
      : DependentSimpleEditor V E StateCategory

    partial-function
      : DependentSimplePartialFunction StateCategory C'

  bool-function
    : DependentSimpleBoolFunction StateCategory
  bool-function
    = dependent-simple-partial-function-bool partial-function

-- ### DependentSimpleSplitEditor

-- #### Definition

record DependentSimpleSplitEditor
  {n : ℕ}
  (V : ViewStack)
  (E : EventStack)
  {C : ChainCategory n}
  (C' : DependentSimpleCategory C)
  : Set₁
  where

  field

    {StateCategory}
      : DependentSimpleCategory C

    editor
      : DependentSimpleEditor V E StateCategory

    split-functor
      : DependentSimpleSplitFunctor StateCategory C'

  partial-editor
    : DependentSimplePartialEditor V E
      (dependent-simple-category-set C')
  partial-editor
    = record
    { editor
      = editor
    ; partial-function
      = dependent-simple-split-functor-partial split-functor
    }

  bool-function
    : DependentSimpleBoolFunction StateCategory
  bool-function
    = dependent-simple-split-functor-bool split-functor

-- #### Conversion

dependent-split-editor-simple
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentSplitEditor V E C'
  → DependentSimpleSplitEditor V E
    (dependent-category-simple C')
dependent-split-editor-simple e
  = record
  { editor
    = dependent-editor-simple
      (DependentSplitEditor.editor e)
  ; split-functor
    = dependent-split-functor-simple
      (DependentSplitEditor.split-functor e)
  }

-- ### DependentSimpleMainEditor

record DependentSimpleMainEditor
  {n : ℕ}
  (V : ViewStack)
  (E : EventStack)
  (S : Set)
  (C : ChainCategory n)
  : Set₁
  where

  field

    {StateCategory}
      : DependentSimpleCategory C

    editor
      : DependentSimpleEditor V E StateCategory

    state-encoding
      : DependentSimpleEncoding StateCategory S

    bool-function
      : DependentSimpleBoolFunction StateCategory

-- ### DependentSimpleInnerEditor

-- #### Definition

record DependentSimpleInnerEditor
  {n : ℕ}
  (V : ViewStack)
  (E : EventStack)
  (S P : Set)
  {C : ChainCategory n}
  (C' : DependentSimpleCategory C)
  : Set₁
  where

  field

    {StateCategory}
      : DependentSimpleCategory C

    editor
      : DependentSimpleEditor V E StateCategory

    state-encoding
      : DependentSimpleEncoding StateCategory S

    pure-encoding
      : DependentSimpleEncoding C' P

    split-functor
      : DependentSimpleSplitFunctor StateCategory C'

  split-editor
    : DependentSimpleSplitEditor V E C'
  split-editor
    = record
    { editor
      = editor
    ; split-functor
      = split-functor
    }

  partial-editor
    : DependentSimplePartialEditor V E
      (dependent-simple-category-set C')
  partial-editor
    = record
    { editor
      = editor
    ; partial-function
      = dependent-simple-split-functor-partial split-functor
    }

  bool-function
    : DependentSimpleBoolFunction StateCategory
  bool-function
    = dependent-simple-split-functor-bool split-functor

-- #### Conversion

dependent-inner-editor-simple
  : {n : ℕ}
  → {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentInnerEditor V E S P C'
  → DependentSimpleInnerEditor V E S P
    (dependent-category-simple C')
dependent-inner-editor-simple e
  = record
  { editor
    = dependent-editor-simple
      (DependentInnerEditor.editor e)
  ; state-encoding
    = dependent-encoding-simple
      (DependentInnerEditor.state-encoding e)
  ; pure-encoding
    = dependent-encoding-simple
      (DependentInnerEditor.pure-encoding e)
  ; split-functor
    = dependent-split-functor-simple
      (DependentInnerEditor.split-functor e)
  }

-- ## Editors (nondependent)

-- ### SplitEditor

-- #### Definition

SplitEditor
  : ViewStack
  → EventStack
  → Category
  → Set₁
SplitEditor V E
  = DependentSplitEditor V E {C = nil}

-- #### Module

module SplitEditor
  {V : ViewStack}
  {E : EventStack}
  {C : Category}
  (e : SplitEditor V E C)
  where

  open DependentSplitEditor e public

  open Category StateCategory public using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    ; identity
      to state-identity
    ; compose
      to state-compose
    ; precompose
      to state-precompose
    ; postcompose
      to state-postcompose
    ; associative
      to state-associative
    )

  open Editor editor public

  open SplitFunctor split-functor public
    hiding (bool-function)

  draw-pure
    : Category.Object C
    → ViewStack.View V
  draw-pure x
    = draw (unbase x)

-- ### InnerEditor

-- #### Definition

InnerEditor
  : ViewStack
  → EventStack
  → Set
  → Set
  → Category
  → Set₁
InnerEditor V E S P
  = DependentInnerEditor V E S P {C = nil}

-- #### Module

module InnerEditor
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C : Category}
  (e : InnerEditor V E S P C)
  where

  open DependentInnerEditor e public

  open Category StateCategory public using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    ; identity
      to state-identity
    ; compose
      to state-compose
    ; precompose
      to state-precompose
    ; postcompose
      to state-postcompose
    ; associative
      to state-associative
    )

  open Editor editor public

  open Encoding state-encoding public using () renaming
    ( encode
      to state-encode
    ; decode
      to state-decode
    ; decode-encode
      to state-decode-encode
    )

  open Encoding pure-encoding public using () renaming
    ( encode
      to pure-encode
    ; decode
      to pure-decode
    ; decode-encode
      to pure-decode-encode
    )

  open SplitFunctor split-functor public
    hiding (bool-function)

  draw-pure
    : Category.Object C
    → ViewStack.View V
  draw-pure x
    = draw (unbase x)

-- ### SimplePartialEditor

-- #### Definition

SimplePartialEditor
  : ViewStack
  → EventStack
  → Set
  → Set₁
SimplePartialEditor V E
  = DependentSimplePartialEditor V E {C = nil}

-- #### Module

module SimplePartialEditor
  {V : ViewStack}
  {E : EventStack}
  {A : Set}
  (e : SimplePartialEditor V E A)
  where

  open DependentSimplePartialEditor e public renaming
    ( StateCategory
      to State
    )

  open PartialFunction partial-function public
    hiding (bool-function)

-- ### SimpleSplitEditor

-- #### Definition

SimpleSplitEditor
  : ViewStack
  → EventStack
  → Set
  → Set₁
SimpleSplitEditor V E
  = DependentSimpleSplitEditor V E {C = nil}

-- #### Module

module SimpleSplitEditor
  {V : ViewStack}
  {E : EventStack}
  {A : Set}
  (e : SimpleSplitEditor V E A)
  where

  open DependentSimpleSplitEditor e public renaming
    ( StateCategory
      to State
    ; split-functor
      to split-function
    )

  open SplitFunction split-function public
    hiding (bool-function)

  draw-pure
    : A
    → ViewStack.View V
  draw-pure x
    = simple-editor-draw editor (unbase x)

-- #### Conversion

split-editor-simple
  : {V : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → SplitEditor V E C
  → SimpleSplitEditor V E
    (Category.Object C)
split-editor-simple
  = dependent-split-editor-simple

-- ### SimpleMainEditor

-- #### Definition

SimpleMainEditor
  : ViewStack
  → EventStack
  → Set
  → Set₁
SimpleMainEditor V E S
  = DependentSimpleMainEditor {n = zero} V E S nil

-- #### Module

module SimpleMainEditor
  {V : ViewStack}
  {E : EventStack}
  {S : Set}
  (e : SimpleMainEditor V E S)
  where

  open DependentSimpleMainEditor e public renaming
    ( StateCategory
      to State
    )

  open Encoding state-encoding public using () renaming
    ( encode
      to state-encode
    ; decode
      to state-decode
    ; decode-encode
      to state-decode-encode
    )

-- ### SimpleInnerEditor

-- #### Definition

SimpleInnerEditor
  : ViewStack
  → EventStack
  → Set
  → Set
  → Set
  → Set₁
SimpleInnerEditor V E S P
  = DependentSimpleInnerEditor V E S P {C = nil}

-- #### Module

module SimpleInnerEditor
  {V : ViewStack}
  {E : EventStack}
  {S P A : Set}
  (e : SimpleInnerEditor V E S P A)
  where

  open DependentSimpleInnerEditor e public renaming
    ( StateCategory
      to State
    ; split-functor
      to split-function
    )

  open Encoding state-encoding public using () renaming
    ( encode
      to state-encode
    ; decode
      to state-decode
    ; decode-encode
      to state-decode-encode
    )

  open Encoding pure-encoding public using () renaming
    ( encode
      to pure-encode
    ; decode
      to pure-decode
    ; decode-encode
      to pure-decode-encode
    )

  open SplitFunction split-function public
    hiding (bool-function)

  draw-pure
    : A
    → ViewStack.View V
  draw-pure x
    = simple-editor-draw editor (unbase x)

-- #### Conversion

inner-editor-simple
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {C : Category}
  → InnerEditor V E S P C
  → SimpleInnerEditor V E S P
    (Category.Object C)
inner-editor-simple
  = dependent-inner-editor-simple

