module Prover.Editor.Flat.Proof.Meta where

open import Editor.Flat
  using (FlatEditor)
open import Editor.Flat.Map.Event
  using (flat-editor-map-event)
open import Editor.Simple.Flatten
  using (simple-partial-editor-flatten)
open import Stack.Flat
  using (FlatEventStack; FlatEventStackMap)
open import Stack.Flatten
  using (event-stack-flatten)

open import Prover.Data.Bool
  using (false)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Function
  using (_$_; id)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Sigma
  using (_×_)
open import Prover.Data.Sum
  using (ι₁; ι₂)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Editor.Simple.Proof.Meta
  using (simple-partial-editor-proof-meta)
open import Prover.Event.Flat.Proof.Meta
  using (FlatProofMetaMode)
open import Prover.Event.Proof.Meta
  using (ProofMetaMode)
open import Prover.Stack.Flat.Proof.Meta
  using (flat-event-stack-proof-meta)
open import Prover.Stack.Flat.Window
  using (flat-view-stack-window)
open import Prover.Stack.Proof.Meta
  using (event-stack-proof-meta)

-- ## FlatEditor

-- ### Event

module FlatEventStackMapProofMeta where

  mode
    : FlatEventStack.Mode (event-stack-flatten event-stack-proof-meta)
    → FlatEventStack.Mode flat-event-stack-proof-meta
  mode (ι₁ ProofMetaMode.nat)
    = FlatProofMetaMode.nat
  mode (ι₁ ProofMetaMode.formula)
    = FlatProofMetaMode.formula
  mode (ι₂ _)
    = FlatProofMetaMode.text

  event
    : (m : FlatEventStack.Mode (event-stack-flatten event-stack-proof-meta))
    → FlatEventStack.Event flat-event-stack-proof-meta (mode m)
    → FlatEventStack.Event (event-stack-flatten event-stack-proof-meta) m
  event (ι₁ ProofMetaMode.nat)
    = id
  event (ι₁ ProofMetaMode.formula)
    = id
  event (ι₂ _)
    = id

flat-event-stack-map-proof-meta
  : FlatEventStackMap
    (event-stack-flatten event-stack-proof-meta)
    flat-event-stack-proof-meta
flat-event-stack-map-proof-meta
  = record {FlatEventStackMapProofMeta}

-- ### Editor

flat-editor-proof-meta
  : (ss : Symbols)
  → (vs : Variables)
  → FlatEditor
    flat-view-stack-window
    flat-event-stack-proof-meta
    (Meta × Formula ss vs false)
flat-editor-proof-meta ss vs
  = flat-editor-map-event flat-event-stack-map-proof-meta
  $ simple-partial-editor-flatten
  $ simple-partial-editor-proof-meta ss vs

