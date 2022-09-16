module Prover.Client where

open import Client.Brick
  using (Attribute; AttributeName; Widget; attribute-background;
    attribute-foreground; attribute-name; black; bright-green; bright-red;
    empty-line; green; horizontal-box; pad-right; string; text; text-with;
    vertical; vertical-box; viewport; with-attribute)

open import Prover.Data.Bool
  using (Bool; false; true)
open import Prover.Data.Fin
  using (Fin; suc; zero)
open import Prover.Data.Function
  using (_$_)
open import Prover.Data.List
  using (List; []; _∷_; _!_)
open import Prover.Data.Maybe
  using (just; nothing)
open import Prover.Data.Sigma
  using (_×_; _,_)
open import Prover.Data.String
  using (String)
open import Prover.View.Command
  using (Command; CommandPath; command)
open import Prover.View.Interface
  using (Interface; InterfacePath; command; interface; nothing; window)
open import Prover.View.Line
  using (Line; LinePath; line)
open import Prover.View.RichText
  using (RichText; RichTextPath; plain; style)
open import Prover.View.Style
  using (Style)
open import Prover.View.Window
  using (Window; WindowPath; go; window)

-- ## Attributes

attribute-complete
  : AttributeName
attribute-complete
  = attribute-name "complete"

attribute-highlight
  : AttributeName
attribute-highlight
  = attribute-name "highlight"

attribute-incomplete
  : AttributeName
attribute-incomplete
  = attribute-name "incomplete"

attribute-margin
  : AttributeName
attribute-margin
  = attribute-name "margin"

attribute-meta
  : AttributeName
attribute-meta
  = attribute-name "meta"

attribute-tree
  : AttributeName
attribute-tree
  = attribute-name "tree"

attributes'
  : List (AttributeName × Attribute)
attributes'
  = (attribute-complete
    , attribute-foreground green)
  ∷ (attribute-highlight
    , attribute-background black)
  ∷ (attribute-incomplete
    , attribute-foreground bright-red)
  ∷ (attribute-margin
    , attribute-background black)
  ∷ (attribute-meta
    , attribute-foreground bright-green)
  ∷ (attribute-tree
    , attribute-foreground bright-green)
  ∷ []

-- ## Widgets

flag
  : Bool
  → String
flag false
  = " ● "
flag true
  = "   "

margin
  : Bool
  → Widget
margin b
  = with-attribute attribute-margin
  $ with-attribute attribute-incomplete
  $ string (flag b)

status
  : Bool
  → Widget
status false
  = with-attribute attribute-incomplete
  $ string " ● "
status true
  = with-attribute attribute-complete
  $ string " ● "

status-bar
  : Bool
  → String
  → Widget
status-bar b s
  = with-attribute attribute-margin
  $ pad-right (horizontal-box (status b ∷ string " " ∷ string s ∷ []))

-- ## Draw

-- ### Style

draw-style
  : Style
  → Widget
  → Widget
draw-style Style.highlight
  = with-attribute attribute-highlight
draw-style Style.meta
  = with-attribute attribute-meta
draw-style Style.tree
  = with-attribute attribute-tree

-- ### RichText

draw-rich-text
  : RichText
  → Widget

draw-rich-texts
  : List RichText
  → List Widget

draw-rich-text (RichText.plain t)
  = text t
draw-rich-text (RichText.texts ts)
  = horizontal-box (draw-rich-texts ts)
draw-rich-text (RichText.style s t)
  = draw-style s (draw-rich-text t)

draw-rich-texts []
  = []
draw-rich-texts (t ∷ ts)
  = draw-rich-text t ∷ draw-rich-texts ts

draw-rich-text-with
  : (t : RichText)
  → RichTextPath t
  → Widget

draw-rich-texts-with
  : (ts : List RichText)
  → (k : Fin (List.length ts))
  → RichTextPath (ts ! k)
  → List Widget

draw-rich-text-with (RichText.plain t) (plain tp)
  = text-with t tp
draw-rich-text-with (RichText.texts ts) (RichTextPath.text k tp)
  = horizontal-box (draw-rich-texts-with ts k tp)
draw-rich-text-with (RichText.style s t) (style tp)
  = draw-style s (draw-rich-text-with t tp)

draw-rich-texts-with (t ∷ ts) zero tp
  = draw-rich-text-with t tp ∷ draw-rich-texts ts
draw-rich-texts-with (t ∷ ts) (suc k) tp
  = draw-rich-text t ∷ draw-rich-texts-with ts k tp

-- ### Line

draw-line
  : Line
  → Widget
draw-line (line s t)
  = horizontal-box (margin s ∷ string " " ∷ draw-rich-text t ∷ [])

draw-lines
  : List Line
  → List Widget
draw-lines
  = List.map draw-line

draw-line-with
  : (l : Line)
  → LinePath l
  → Widget
draw-line-with (line s t) lp
  = horizontal-box (margin s ∷ string " " ∷ draw-rich-text-with t lp ∷ [])

draw-lines-with
  : (ls : List Line)
  → (k : Fin (List.length ls))
  → LinePath (ls ! k)
  → List Widget
draw-lines-with (l ∷ ls) zero lp
  = draw-line-with l lp ∷ draw-lines ls
draw-lines-with (l ∷ ls) (suc k) lp
  = draw-line l ∷ draw-lines-with ls k lp

-- ### Window

draw-window-head
  : Window
  → Widget
draw-window-head (window n c ls)
  = vertical-box
  $ viewport vertical (vertical-box (draw-lines ls))
  ∷ status-bar c n
  ∷ []

draw-window-tail
  : Window
  → Widget
draw-window-tail (window n c ls)
  = vertical-box
  $ vertical-box (draw-lines ls)
  ∷ status-bar c n
  ∷ []

draw-windows-tail
  : List Window
  → List Widget
draw-windows-tail
  = List.map draw-window-tail

draw-windows
  : List Window
  → List Widget
draw-windows []
  = []
draw-windows (p ∷ ps)
  = draw-window-head p ∷ draw-windows-tail ps

draw-window-head-with
  : (p : Window)
  → WindowPath p
  → Widget
draw-window-head-with (window n c ls) (go k lp)
  = vertical-box
  $ viewport vertical (vertical-box (draw-lines-with ls k lp))
  ∷ status-bar c n
  ∷ []

draw-window-tail-with
  : (p : Window)
  → WindowPath p
  → Widget
draw-window-tail-with (window n c ls) (go k lp)
  = vertical-box
  $ vertical-box (draw-lines-with ls k lp)
  ∷ status-bar c n
  ∷ []

draw-windows-tail-with
  : (ps : List Window)
  → (k : Fin (List.length ps))
  → WindowPath (ps ! k)
  → List Widget
draw-windows-tail-with (p ∷ ps) zero pp
  = draw-window-tail-with p pp ∷ draw-windows-tail ps
draw-windows-tail-with (p ∷ ps) (suc k) pp
  = draw-window-tail p ∷ draw-windows-tail-with ps k pp

draw-windows-with
  : (ps : List Window)
  → (k : Fin (List.length ps))
  → WindowPath (ps ! k)
  → List Widget
draw-windows-with (p ∷ ps) zero pp
  = draw-window-head-with p pp ∷ draw-windows-tail ps
draw-windows-with (p ∷ ps) (suc k) pp
  = draw-window-head p ∷ draw-windows-tail-with ps k pp

-- ### Command

draw-command-with
  : (c : Command)
  → CommandPath c
  → Widget
draw-command-with (command p t) cp
  = horizontal-box (string p ∷ string ": " ∷ text-with t cp ∷ [])

-- ### Interface

draw-interface-with
  : (w : Interface)
  → InterfacePath w
  → Widget
draw-interface-with (interface nothing ps) nothing
  = vertical-box (List.snoc (draw-windows ps) empty-line)
draw-interface-with (interface nothing ps) (window k pp)
  = vertical-box (List.snoc (draw-windows-with ps k pp) empty-line)
draw-interface-with (interface (just c) ps) (command cp)
  = vertical-box (List.snoc (draw-windows ps) (draw-command-with c cp))

