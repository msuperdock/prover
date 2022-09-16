module Prover.Draw.Meta where

open import Prover.Data.Text
  using (Text)
open import Prover.View.RichText
  using (RichText)
open import Prover.View.Style
  using (Style)

draw-meta
  : Text
  → RichText
draw-meta t
  = RichText.style Style.meta (RichText.wrap "[" "]" (RichText.plain t))

draw-meta-empty
  : RichText
draw-meta-empty
  = RichText.style Style.meta (RichText.wrap "[" "]" (RichText.string "_"))

