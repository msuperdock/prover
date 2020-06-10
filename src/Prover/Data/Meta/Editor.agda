module Prover.Data.Meta.Editor where

open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Number.Editor
  using (NumberEventStack; number-partial-editor)
open import Prover.Editor
  using (PartialEditor; ViewStack; ViewStackMap)
open import Prover.Editor.Base
  using (BaseViewStack; BaseViewStackMap)
open import Prover.Editor.Lift
  using (view-stack-map-lift)
open import Prover.Editor.Map
  using (partial-editor-map-view)
open import Prover.View.Style
  using (Style)
open import Prover.View.Text
  using (PlainText; PlainTextBaseViewStack; PlainTextViewStack; RichText;
    RichTextBaseViewStack; RichTextViewStack; plain; style; text)
open import Prover.Prelude

-- ## Draw

draw-meta
  : PlainText
  → RichText
draw-meta
  = RichText.style Style.meta
  ∘ RichText.wrap "[" "]"
  ∘ RichText.plain

-- ## Editor

module MetaBaseViewStackMap where

  view
    : BaseViewStack.View PlainTextBaseViewStack
    → BaseViewStack.View RichTextBaseViewStack
  view
    = draw-meta

  view-with
    : (v : BaseViewStack.View PlainTextBaseViewStack)
    → BaseViewStack.ViewPath PlainTextBaseViewStack v
    → BaseViewStack.View RichTextBaseViewStack
  view-with v _
    = view v
  
  view-path
    : (v : BaseViewStack.View PlainTextBaseViewStack)
    → (vp : BaseViewStack.ViewPath PlainTextBaseViewStack v)
    → BaseViewStack.ViewPath RichTextBaseViewStack (view-with v vp)
  view-path _ nothing
    = style (text (suc (suc zero)) (plain zero))
  view-path _ (just tp)
    = style (text (suc zero) (plain tp))

meta-base-view-stack-map
  : BaseViewStackMap
    PlainTextBaseViewStack
    RichTextBaseViewStack
meta-base-view-stack-map
  = record {MetaBaseViewStackMap}

meta-view-stack-map
  : ViewStackMap
    PlainTextViewStack
    RichTextViewStack
meta-view-stack-map
  = view-stack-map-lift
    meta-base-view-stack-map

meta-partial-editor
  : PartialEditor
    RichTextViewStack
    NumberEventStack
    Meta
meta-partial-editor
  = partial-editor-map-view meta-view-stack-map
  $ number-partial-editor

