module Prover.Client.Brick where

open import Prover.View.Command
  using (Command; CommandPath; command)
open import Prover.View.Interface
  using (Interface; InterfacePath; command; interface; nothing; window)
open import Prover.View.Line
  using (Line; LinePath; line)
open import Prover.View.Style
  using (Style)
open import Prover.View.Text
  using (PlainText; PlainTextPath; RichText; RichTextPath; plain; style; text)
open import Prover.View.Window
  using (Window; WindowPath; go; window)
open import Prover.Prelude

open List
  using ([]; _∷_; _!_)

-- ## Types

data ViewportType
  : Set
  where

  horizontal
    : ViewportType

  vertical
    : ViewportType
  
  both
    : ViewportType

data InputEvent
  : Set
  where

  escape
    : InputEvent

  return
    : InputEvent

  backspace
    : InputEvent

  delete
    : InputEvent

  up
    : InputEvent

  down
    : InputEvent

  left
    : InputEvent

  right
    : InputEvent

  char
    : Char
    → InputEvent

-- ## Postulates

postulate
  
  -- ### Types

  App
    : Set
    → Set

  Attribute
    : Set

  AttributeMap
    : Set

  AttributeName
    : Set

  BrickEvent
    : Set

  Color
    : Set

  CursorLocation
    : Set

  EventM
    : Set
    → Set

  Location
    : Set

  Next
    : Set
    → Set

  Padding
    : Set

  Widget
    : Set

  -- ### Functions

  app
    : {S : Set}
    → (S → List' Widget)
    → (S → List' CursorLocation → Maybe CursorLocation)
    → (S → BrickEvent → EventM (Next S))
    → (S → EventM S)
    → (S → AttributeMap)
    → App S

  attribute-map
    : Attribute
    → List' (Pair AttributeName Attribute)
    → AttributeMap

  attribute-name
    : String
    → AttributeName

  continue
    : {S : Set}
    → S
    → EventM (Next S)

  default-attribute
    : Attribute

  default-main
    : {S : Set}
    → App S
    → S
    → IO S

  event-bind
    : {A B : Set}
    → EventM A
    → (A → EventM B)
    → EventM B

  event-pure
    : {S : Set}
    → S
    → EventM S

  from-brick-event
    : BrickEvent
    → Maybe InputEvent

  halt
    : {S : Set}
    → S
    → EventM (Next S)

  horizontal-box'
    : List' Widget
    → Widget

  liftIO
    : {A : Set}
    → IO A
    → EventM A

  location
    : ℕ
    → ℕ
    → Location

  pad-right-with
    : Padding
    → Widget
    → Widget

  padding-max
    : Padding

  show-cursor
    : Location
    → Widget
    → Widget

  string 
    : String
    → Widget

  vertical-box'
    : List' Widget
    → Widget

  viewport
    : ViewportType
    → Widget
    → Widget

  with-attribute
    : AttributeName
    → Widget
    → Widget

  with-background
    : Attribute
    → Color
    → Attribute

  with-foreground
    : Attribute
    → Color
    → Attribute

  -- ### Colors

  black
    : Color

  green
    : Color

  bright-green
    : Color

  bright-red
    : Color

-- ## Foreign

-- ### Imports

{-# FOREIGN GHC
  import Brick.AttrMap
    (AttrMap, AttrName, attrMap)
  import Brick.Main
    (App (App), continue, defaultMain, halt)
  import Brick.Types
    (BrickEvent (VtyEvent), CursorLocation, EventM, Location (Location), Next,
      Padding (Max), ViewportType (Both, Horizontal, Vertical), Widget)
  import Brick.Widgets.Core
    (hBox, padRight, showCursor, txt, vBox, viewport, withDefAttr)
  import Control.Monad.IO.Class
    (liftIO)
  import Data.String
    (fromString)
  import Data.Text
    (unpack)
  import Graphics.Vty.Attributes
    (Attr, Color, black, brightGreen, brightRed, defAttr, green, withBackColor,
      withForeColor)
  import Graphics.Vty.Input.Events
    (Event (EvKey), Key (KBS, KChar, KDel, KDown, KEnter, KEsc, KLeft, KRight,
      KUp))
  import Prelude
    hiding (Left, Right)
#-}

-- ### Definitions

{-# FOREIGN GHC
  type SimpleApp s
    = App s () ()

  data InputEvent
    = Escape
    | Return
    | Backspace
    | Delete
    | Up
    | Down
    | Left
    | Right
    | Char Char

  fromBrickEvent
    :: BrickEvent () ()
    -> Maybe InputEvent
  fromBrickEvent (VtyEvent (EvKey KEsc _))
    = Just Escape
  fromBrickEvent (VtyEvent (EvKey KEnter _))
    = Just Return
  fromBrickEvent (VtyEvent (EvKey KBS _))
    = Just Backspace
  fromBrickEvent (VtyEvent (EvKey KDel _))
    = Just Delete
  fromBrickEvent (VtyEvent (EvKey KUp _))
    = Just Up
  fromBrickEvent (VtyEvent (EvKey KDown _))
    = Just Down
  fromBrickEvent (VtyEvent (EvKey KLeft _))
    = Just Left
  fromBrickEvent (VtyEvent (EvKey KRight _))
    = Just Right
  fromBrickEvent (VtyEvent (EvKey (KChar c) _))
    = Just (Char c)
  fromBrickEvent _
    = Nothing

  location
    :: Integer
    -> Integer
    -> Location
  location c r
    = Location (fromIntegral c, fromIntegral r)
#-}

-- ### Data

{-# COMPILE GHC InputEvent
  = data InputEvent
    ( Escape
    | Return
    | Backspace
    | Delete
    | Up
    | Down
    | Left
    | Right
    | Char
    )
#-}

{-# COMPILE GHC ViewportType
  = data ViewportType
    ( Horizontal
    | Vertical
    | Both
    )
#-}

-- ### Types

{-# COMPILE GHC App
  = type SimpleApp #-}
{-# COMPILE GHC Attribute
  = type Attr #-}
{-# COMPILE GHC AttributeMap
  = type AttrMap #-}
{-# COMPILE GHC AttributeName
  = type AttrName #-}
{-# COMPILE GHC BrickEvent
  = type BrickEvent () () #-}
{-# COMPILE GHC Color
  = type Color #-}
{-# COMPILE GHC CursorLocation
  = type CursorLocation () #-}
{-# COMPILE GHC EventM
  = type EventM () #-}
{-# COMPILE GHC Location
  = type Location #-}
{-# COMPILE GHC Next
  = type Next #-}
{-# COMPILE GHC Padding
  = type Padding #-}
{-# COMPILE GHC Widget
  = type Widget () #-}

-- ### Functions

{-# COMPILE GHC app
  = \ _ -> App #-}
{-# COMPILE GHC attribute-map
  = attrMap #-}
{-# COMPILE GHC attribute-name
  = fromString . unpack #-}
{-# COMPILE GHC continue
  = \ _ -> continue #-}
{-# COMPILE GHC default-attribute
  = defAttr #-}
{-# COMPILE GHC default-main
  = \ _ -> defaultMain #-}
{-# COMPILE GHC event-bind
  = \ _ _ -> (>>=) #-}
{-# COMPILE GHC event-pure
  = \ _ -> pure #-}
{-# COMPILE GHC from-brick-event
  = fromBrickEvent #-}
{-# COMPILE GHC halt
  = \ _ -> halt #-}
{-# COMPILE GHC horizontal-box'
  = hBox #-}
{-# COMPILE GHC liftIO
  = \ _ -> liftIO #-}
{-# COMPILE GHC location
  = location #-}
{-# COMPILE GHC pad-right-with
  = padRight #-}
{-# COMPILE GHC padding-max
  = Max #-}
{-# COMPILE GHC show-cursor
  = showCursor () #-}
{-# COMPILE GHC string
  = txt #-}
{-# COMPILE GHC vertical-box'
  = vBox #-}
{-# COMPILE GHC viewport
  = viewport () #-}
{-# COMPILE GHC with-attribute
  = withDefAttr #-}
{-# COMPILE GHC with-background
  = withBackColor #-}
{-# COMPILE GHC with-foreground
  = withForeColor #-}

-- ### Colors

{-# COMPILE GHC black
  = black #-}
{-# COMPILE GHC green
  = green #-}

{-# COMPILE GHC bright-green
  = brightGreen #-}
{-# COMPILE GHC bright-red
  = brightRed #-}

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

attribute-background
  : Color
  → Attribute
attribute-background
  = with-background default-attribute

attribute-foreground
  : Color
  → Attribute
attribute-foreground
  = with-foreground default-attribute

attribute-list
  : List (Pair AttributeName Attribute)
attribute-list
  = pair attribute-complete
    (attribute-foreground green)
  ∷ pair attribute-highlight
    (attribute-background black)
  ∷ pair attribute-incomplete
    (attribute-foreground bright-red)
  ∷ pair attribute-margin
    (attribute-background black)
  ∷ pair attribute-meta
    (attribute-foreground bright-green)
  ∷ pair attribute-tree
    (attribute-foreground bright-green)
  ∷ []

attributes
  : AttributeMap
attributes
  = attribute-map default-attribute (List.to-builtin attribute-list)

-- ## Widgets

empty-line
  : Widget
empty-line
  = string " "

pad-right
  : Widget
  → Widget
pad-right
  = pad-right-with padding-max

horizontal-box
  : List Widget
  → Widget
horizontal-box ws
  = horizontal-box' (List.to-builtin ws)

vertical-box
  : List Widget
  → Widget
vertical-box ws
  = vertical-box' (List.to-builtin ws)

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

-- ### PlainText

draw-plain-text
  : PlainText
  → Widget
draw-plain-text t
  = string (String.from-list t)

draw-plain-text-with
  : (t : PlainText)
  → PlainTextPath t
  → Widget
draw-plain-text-with t tp
  = show-cursor (location (Fin.to-nat tp) zero) (draw-plain-text t)

-- ### RichText

draw-rich-text
  : RichText
  → Widget

draw-rich-texts
  : List RichText
  → List Widget

draw-rich-text (RichText.plain t)
  = draw-plain-text t
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
  = draw-plain-text-with t tp
draw-rich-text-with (RichText.texts ts) (text k tp)
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
  = horizontal-box (string p ∷ string ": " ∷ draw-plain-text-with t cp ∷ [])

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

