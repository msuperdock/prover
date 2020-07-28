module Prover.View.Tree where

open import Prover.View.Line
  using (Line)
open import Prover.View.Style
  using (Style)
open import Prover.View.Text
  using (PlainText; RichText)
open import Prover.Prelude

open Vec
  using ([]; _∷_; _!_)

open List using () renaming
  ( []
    to []'
  ; _∷_
    to _∷'_
  )

-- ## Definitions

data Tree
  : Set
  where

  leaf
    : Line
    → Tree

  node
    : {n : ℕ}
    → Vec Tree (suc n)
    → Line
    → Tree

data TreePath
  : Tree
  → Set
  where

  stop
    : {t : Tree}
    → TreePath t

  go
    : {n : ℕ}
    → {ts : Vec Tree (suc n)}
    → {l : Line}
    → (k : Fin (suc n))
    → TreePath (ts ! k)
    → TreePath (node ts l)

-- ## Draw

-- ### indent

indent-line
  : PlainText
  → Line
  → Line
indent-line t (Line.line s t')
  = record
  { status
    = s
  ; text
    = RichText.texts (RichText.style Style.tree (RichText.plain t) ∷ t' ∷ [])
  }

indent-lines
  : {n : ℕ}
  → PlainText
  → PlainText
  → Vec Line n
  → Vec Line n
indent-lines _ _ []
  = []
indent-lines _ t (l ∷ [])
  = indent-line t l ∷ []
indent-lines t t' (l ∷ ls@(_ ∷ _))
  = indent-line t l ∷ indent-lines t t' ls

indent-head
  : List Line
  → List Line
indent-head (any ls)
  = any (indent-lines (String.to-list "  ") (String.to-list "┌╸") ls)

indent-tail
  : List Line
  → List Line
indent-tail (any ls)
  = any (indent-lines (String.to-list "│ ") (String.to-list "├╸") ls)

indent-trees
  : List (List Line)
  → List Line
indent-trees []'
  = []'
indent-trees (t ∷' ts)
  = List.concat (indent-head t ∷' List.map indent-tail ts)

-- ### draw

draw-tree
  : Tree
  → List Line

draw-trees
  : {n : ℕ}
  → Vec Tree n
  → List (List Line)

draw-tree (leaf l)
  = l ∷' []'
draw-tree (node ts l)
  = List.snoc (indent-trees (draw-trees ts)) l

draw-trees []
  = []'
draw-trees (t ∷ ts)
  = draw-tree t ∷' draw-trees ts

-- ### draw-with

draw-tree-with
  : (t : Tree)
  → TreePath t
  → List Line

draw-trees-with
  : {n : ℕ}
  → (ts : Vec Tree n)
  → (k : Fin n)
  → TreePath (ts ! k)
  → List (List Line)

draw-tree-with (leaf (Line.line s t)) stop
  = Line.line s (RichText.style Style.highlight t) ∷' []'
draw-tree-with (node ts (Line.line s t)) stop
  = List.snoc (indent-trees (draw-trees ts))
    (Line.line s (RichText.style Style.highlight t))
draw-tree-with (node ts l) (go k tp)
  = List.snoc (indent-trees (draw-trees-with ts k tp)) l

draw-trees-with (t ∷ ts) zero tp
  = draw-tree-with t tp ∷' draw-trees ts
draw-trees-with (t ∷ ts) (suc k) tp
  = draw-tree t ∷' draw-trees-with ts k tp

