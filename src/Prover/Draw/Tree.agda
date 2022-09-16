module Prover.Draw.Tree where

open import Prover.Data.Fin
  using (Fin; suc; zero)
open import Prover.Data.List
  using (List; []; _∷_; _!_)
open import Prover.Data.String
  using (String)
open import Prover.Data.Text
  using (Text)
open import Prover.View.Line
  using (Line; line)
open import Prover.View.RichText
  using (RichText)
open import Prover.View.Style
  using (Style)
open import Prover.View.Tree
  using (Tree; TreePath; go; stop)

-- ## indent

indent-line
  : Text
  → Line
  → Line
indent-line t (line s t')
  = record
  { status
    = s
  ; text
    = RichText.texts (RichText.style Style.tree (RichText.plain t) ∷ t' ∷ [])
  }

indent-lines
  : Text
  → Text
  → List Line
  → List Line
indent-lines _ _ []
  = []
indent-lines _ t (l ∷ [])
  = indent-line t l ∷ []
indent-lines t t' (l ∷ ls)
  = indent-line t l ∷ indent-lines t t' ls

indent-head
  : List Line
  → List Line
indent-head
  = indent-lines
    (String.to-list "  ")
    (String.to-list "┌╸")

indent-tail
  : List Line
  → List Line
indent-tail
  = indent-lines
    (String.to-list "│ ")
    (String.to-list "├╸")

indent-trees
  : List (List Line)
  → List Line
indent-trees []
  = []
indent-trees (t ∷ ts)
  = List.concat (indent-head t ∷ List.map indent-tail ts)

-- ## draw

draw-tree
  : Tree
  → List Line

draw-trees
  : List Tree
  → List (List Line)

draw-tree (Tree.leaf l)
  = l ∷ []
draw-tree (Tree.node ts l)
  = List.snoc (indent-trees (draw-trees ts)) l

draw-trees []
  = []
draw-trees (t ∷ ts)
  = draw-tree t ∷ draw-trees ts

-- ## draw-with

draw-tree-with
  : (t : Tree)
  → TreePath t
  → List Line

draw-trees-with
  : (ts : List Tree)
  → (k : Fin (List.length ts))
  → TreePath (ts ! k)
  → List (List Line)

draw-tree-with (Tree.leaf (line s t)) stop
  = line s (RichText.style Style.highlight t) ∷ []
draw-tree-with (Tree.node ts (line s t)) stop
  = List.snoc (indent-trees (draw-trees ts))
    (line s (RichText.style Style.highlight t))
draw-tree-with (Tree.node ts l) (go k tp)
  = List.snoc (indent-trees (draw-trees-with ts k tp)) l

draw-trees-with (t ∷ ts) zero tp
  = draw-tree-with t tp ∷ draw-trees ts
draw-trees-with (t ∷ ts) (suc k) tp
  = draw-tree t ∷ draw-trees-with ts k tp

