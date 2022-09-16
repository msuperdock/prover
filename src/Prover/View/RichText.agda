module Prover.View.RichText where

open import Prover.Data.Fin
  using (Fin)
open import Prover.Data.List
  using (List; []; _∷_; _!_)
open import Prover.Data.String
  using (String)
open import Prover.Data.Text
  using (Text)
open import Prover.View.Style
  using (Style)

-- ## Internal

module Internal where

  -- ### Definitions
  
  data RichText
    : Set
    where
    
    plain
      : Text
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
      : {t : Text}
      → Fin (Text.length t)
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
  
-- ## Modules

-- ### RichText

RichText
  = Internal.RichText

module RichText where

  open Internal.RichText public

  open Internal public
    using () renaming
    ( rich-text-string
      to string
    ; rich-text-wrap
      to wrap
    )

-- ### RichTextPath

open Internal public
  using (RichTextPath)
open Internal.RichTextPath public

