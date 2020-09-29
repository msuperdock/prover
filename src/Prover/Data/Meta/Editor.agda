module Prover.Data.Meta.Editor where

open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Number.Editor
  using (NumberEventStack; number-simple-partial-editor)
open import Prover.Editor
  using (SimplePartialEditor; ViewStackMap)
open import Prover.Editor.Base
  using (BaseViewStack; BaseViewStackMap)
open import Prover.Editor.Lift
  using (view-stack-map-lift)
open import Prover.Editor.Map.View
  using (simple-partial-editor-map-view)
open import Prover.View.Style
  using (Style)
open import Prover.View.Text
  using (PlainText; PlainTextBaseViewStack; PlainTextViewStack; RichText;
    RichTextBaseViewStack; RichTextViewStack; plain; style; text)
open import Prover.Prelude

open List
  using ([]; _∷_)

-- ## Draw

draw-meta
  : PlainText
  → RichText
draw-meta t
  = RichText.style Style.meta (RichText.wrap "[" "]" (RichText.plain t))

draw-meta-empty
  : RichText
draw-meta-empty
  = RichText.style Style.meta (RichText.wrap "[" "]" (RichText.string "_"))

-- ## Editors

-- ### SimplePartialEditor

module MetaBaseViewStackMap where

  view
    : BaseViewStack.View PlainTextBaseViewStack
    → BaseViewStack.View RichTextBaseViewStack
  view []
    = draw-meta-empty
  view t@(_ ∷ _)
    = draw-meta t

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
  view-path [] nothing
    = style (text (suc zero) (plain zero))
  view-path (_ ∷ _) nothing
    = style (text (suc (suc zero)) (plain zero))
  view-path (_ ∷ _) (just tp)
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

meta-simple-partial-editor
  : SimplePartialEditor
    RichTextViewStack
    NumberEventStack
    Meta
meta-simple-partial-editor
  = simple-partial-editor-map-view meta-view-stack-map
  $ number-simple-partial-editor

