module Prover.Stack.Base.RichText where

open import Stack.Base
  using (BaseViewStack)

open import Prover.View.RichText
  using (RichText; RichTextPath)

-- ## Stacks

-- ### BaseViewStack

base-view-stack-rich-text
  : BaseViewStack
base-view-stack-rich-text
  = record
  { View
    = RichText
  ; ViewPath
    = RichTextPath
  }

