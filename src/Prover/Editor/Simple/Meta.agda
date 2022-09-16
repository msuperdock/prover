module Prover.Editor.Simple.Meta where

open import Editor.Simple
  using (SimplePartialEditor)
open import Editor.Simple.Map.View
  using (simple-partial-editor-map-view)
open import Editor.Simple.Nat
  using (simple-partial-editor-nat)
open import Stack
  using (ViewStackMap)
open import Stack.Base
  using (BaseViewStack; BaseViewStackMap)
open import Stack.Base.Text
  using (base-view-stack-text)
open import Stack.Lift
  using (view-stack-map-lift)
open import Stack.Nat
  using (event-stack-nat)
open import Stack.Text
  using (view-stack-text)

open import Prover.Data.Fin
  using (suc; zero)
open import Prover.Data.Function
  using (_$_)
open import Prover.Data.List
  using ([]; _∷_)
open import Prover.Data.Maybe
  using (just; nothing)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Draw.Meta
  using (draw-meta; draw-meta-empty)
open import Prover.Stack.Base.RichText
  using (base-view-stack-rich-text)
open import Prover.Stack.RichText
  using (view-stack-rich-text)
open import Prover.View.RichText
  using (plain; style; text)

-- ## SimplePartialEditor

-- ### View

module BaseViewStackMapMeta where

  view
    : BaseViewStack.View base-view-stack-text
    → BaseViewStack.View base-view-stack-rich-text
  view []
    = draw-meta-empty
  view t@(_ ∷ _)
    = draw-meta t

  view-with
    : (v : BaseViewStack.View base-view-stack-text)
    → BaseViewStack.ViewPath base-view-stack-text v
    → BaseViewStack.View base-view-stack-rich-text
  view-with v _
    = view v
  
  view-path
    : (v : BaseViewStack.View base-view-stack-text)
    → (vp : BaseViewStack.ViewPath base-view-stack-text v)
    → BaseViewStack.ViewPath base-view-stack-rich-text (view-with v vp)
  view-path [] nothing
    = style (text (suc zero) (plain zero))
  view-path (_ ∷ _) nothing
    = style (text (suc (suc zero)) (plain zero))
  view-path (_ ∷ _) (just tp)
    = style (text (suc zero) (plain tp))

base-view-stack-map-meta
  : BaseViewStackMap
    base-view-stack-text
    base-view-stack-rich-text
base-view-stack-map-meta
  = record {BaseViewStackMapMeta}

view-stack-map-meta
  : ViewStackMap
    view-stack-text
    view-stack-rich-text
view-stack-map-meta
  = view-stack-map-lift
    base-view-stack-map-meta

-- ### Editor

simple-partial-editor-meta
  : SimplePartialEditor
    view-stack-rich-text
    event-stack-nat
    Meta
simple-partial-editor-meta
  = simple-partial-editor-map-view view-stack-map-meta
  $ simple-partial-editor-nat

