module Prover.View.Text where

open import Prover.Editor
  using (ViewStack)
open import Prover.Editor.Base
  using (BaseViewStack)
open import Prover.Editor.Flat
  using (FlatViewStack)
open import Prover.Editor.Flatten
  using (base-view-stack-flatten)
open import Prover.Editor.Lift
  using (view-stack-lift)
open import Prover.View.Style
  using (Style)
open import Prover.Prelude

open List
  using ([]; _∷_; _!_)

-- ## Internal

module Internal where

  -- ### Definitions
  
  PlainText
    : Set
  PlainText
    = List Char
  
  PlainTextPath
    : PlainText
    → Set
  PlainTextPath cs
    = Fin (List.length cs)
  
  data RichText
    : Set
    where
    
    plain
      : PlainText
      → RichText
  
    style
      : Style
      → RichText
      → RichText
  
    texts
      : List RichText
      → RichText
    
  data RichTextPath
    : RichText
    → Set
    where
  
    plain
      : {t : PlainText}
      → PlainTextPath t
      → RichTextPath (plain t)
      
    style
      : {s : Style}
      → {t : RichText}
      → RichTextPath t
      → RichTextPath (style s t)
  
    text
      : {ts : List RichText}
      → (k : Fin (List.length ts))
      → RichTextPath (ts ! k)
      → RichTextPath (texts ts)
    
  -- ### Interface
  
  rich-text-string
    : String
    → RichText
  rich-text-string s
    = RichText.plain (String.to-list s)
  
  rich-text-wrap
    : String
    → String
    → RichText
    → RichText
  rich-text-wrap s₁ s₂ t
    = RichText.texts (rich-text-string s₁ ∷ t ∷ rich-text-string s₂ ∷ [])
  
  -- ### Stacks
  
  PlainTextBaseViewStack
    : BaseViewStack
  PlainTextBaseViewStack
    = record
    { View
      = PlainText
    ; ViewPath
      = λ t → Maybe (PlainTextPath t)
    }

  PlainTextViewStack
    : ViewStack
  PlainTextViewStack
    = view-stack-lift
      PlainTextBaseViewStack

  PlainTextFlatViewStack
    : FlatViewStack
  PlainTextFlatViewStack
    = base-view-stack-flatten
      PlainTextBaseViewStack

  RichTextBaseViewStack
    : BaseViewStack
  RichTextBaseViewStack
    = record
    { View
      = RichText
    ; ViewPath
      = RichTextPath
    }

  RichTextViewStack
    : ViewStack
  RichTextViewStack
    = view-stack-lift
      RichTextBaseViewStack

-- ## Modules

-- ### PlainText

open Internal public
  using (PlainText; PlainTextBaseViewStack; PlainTextFlatViewStack;
    PlainTextViewStack)

-- ### RichText

RichText
  = Internal.RichText

open Internal public
  using (RichTextBaseViewStack; RichTextViewStack)

module RichText where

  open Internal.RichText public

  open Internal public using () renaming
    ( rich-text-string
      to string
    ; rich-text-wrap
      to wrap
    )

-- ### PlainTextPath

open Internal public
  using (PlainTextPath)

-- ### RichTextPath

open Internal public
  using (RichTextPath)
open Internal.RichTextPath public

