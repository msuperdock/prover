module Prover.Editor.Flat.Command where

open import Editor.Flat
  using (FlatEditor)
open import Editor.Flat.Map.View
  using (flat-editor-map-view)
open import Editor.Flat.Text
  using (flat-editor-text)
open import Stack.Flat
  using (FlatViewStack; FlatViewStackMap)
open import Stack.Flat.Text
  using (flat-event-stack-text; flat-view-stack-text)

open import Prover.Data.Fin
  using (Fin)
open import Prover.Data.Function
  using (_$_)
open import Prover.Data.List
  using (List)
open import Prover.Data.Maybe
  using (just; nothing)
open import Prover.Data.String
  using (String)
open import Prover.Data.Text
  using (Text)
open import Prover.Stack.Flat.Command
  using (flat-view-stack-command)
open import Prover.View.Command
  using (command)

-- ## FlatEditor

-- ### View

module FlatViewStackMapCommand
  (p : String)
  where

  view-with
    : (v : FlatViewStack.View flat-view-stack-text)
    → FlatViewStack.ViewPath flat-view-stack-text v
    → FlatViewStack.View flat-view-stack-command
  view-with cs nothing
    = command p (List.snoc cs ' ')
  view-with t (just _)
    = command p t

  view-path
    : (v : FlatViewStack.View flat-view-stack-text)
    → (vp : FlatViewStack.ViewPath flat-view-stack-text v)
    → FlatViewStack.ViewPath flat-view-stack-command (view-with v vp)
  view-path cs nothing
    = Fin.maximum (List.length cs)
  view-path _ (just k)
    = k

-- Takes a prompt string, not including colon or space.
flat-view-stack-map-command
  : String
  → FlatViewStackMap
    flat-view-stack-text
    flat-view-stack-command
flat-view-stack-map-command p
  = record {FlatViewStackMapCommand p}

-- ### Editor

-- Takes a prompt string, not including colon or space.
flat-editor-command
  : String
  → FlatEditor
    flat-view-stack-command
    flat-event-stack-text
    Text
flat-editor-command s
  = flat-editor-map-view (flat-view-stack-map-command s)
  $ flat-editor-text

