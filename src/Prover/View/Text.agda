module Prover.View.Text where

open import Prover.Editor
  using (ViewStack)
open import Prover.Editor.Base
  using (BaseViewStack)
open import Prover.Editor.Lift
  using (view-stack-lift)
open import Prover.View.Style
  using (Style)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definitions
  
  PlainText
    : Set
  PlainText
    = Any (Vec Char)
  
  PlainTextPath
    : PlainText
    → Set
  PlainTextPath (any {n} cs)
    = Fin n
  
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
      : {n : ℕ}
      → Vec RichText n
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
      : {n : ℕ}
      → {ts : Vec RichText n}
      → (k : Fin n)
      → RichTextPath (ts ! k)
      → RichTextPath (texts ts)
    
  -- ### Interface
  
  rich-text-string
    : String
    → RichText
  rich-text-string s
    = RichText.plain (String.to-vec s)
  
  rich-text-wrap
    : String
    → String
    → RichText
    → RichText
  rich-text-wrap s₁ s₂ t
    = RichText.texts (rich-text-string s₁ ∷ t ∷ rich-text-string s₂ ∷ [])
  
  -- ### Stacks
  
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
  using (PlainText)

-- ### RichText

RichText
  : Set
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
