module Prover.Editor.Child where

open import Prover.Category
  using (Category)
open import Prover.Category.Unit
  using (module CategoryUnit; category-unit)
open import Prover.Editor.Base
  using (BaseEditor; BaseEventStack; BaseViewStack; SimpleBaseEditor;
    base-editor-from-simple)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatViewStack)
open import Prover.Prelude

-- ## ChildEditor

record ChildEditor
  {V : BaseViewStack}
  {E : BaseEventStack}
  {C : Category}
  (W : FlatViewStack)
  (F : FlatEventStack)
  (e : BaseEditor V E C)
  : Set₁
  where

  open Category C using () renaming
    ( Object
      to BaseState
    ; Arrow
      to BaseStateArrow
    ; identity
      to base-state-identity
    ; compose
      to base-state-compose
    ; precompose
      to base-state-precompose
    ; postcompose
      to base-state-postcompose
    ; associative
      to base-state-associative
    )

  open BaseEditor e using () renaming
    ( StatePath
      to BaseStatePath
    )

  field

    Result
      : (s : BaseState)
      → BaseStatePath s
      → Set

    flat-editor
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → FlatEditor W F (Result s sp)

    update
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Result s sp
      → s' ∈ BaseState × sp' ∈ BaseStatePath s' × BaseStateArrow s s'

-- ## SimpleChildEditor

-- ### Definition

record SimpleChildEditor
  {V : BaseViewStack}
  {E : BaseEventStack}
  {A : Set}
  (W : FlatViewStack)
  (F : FlatEventStack)
  (e : SimpleBaseEditor V E A)
  : Set₁
  where

  private

    BaseState
      : Set
    BaseState
      = A

  open SimpleBaseEditor e using () renaming
    ( StatePath
      to BaseStatePath
    )

  field

    Result
      : (s : BaseState)
      → BaseStatePath s
      → Set

    flat-editor
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → FlatEditor W F (Result s sp)

    update
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Result s sp
      → Σ BaseState BaseStatePath

-- ### Conversion

module _
  {V : BaseViewStack}
  {W : FlatViewStack}
  {E : BaseEventStack}
  {F : FlatEventStack}
  {A : Set}
  {e : SimpleBaseEditor V E A}
  where

  module ChildEditorFromSimple
    (e' : SimpleChildEditor W F e)
    where

    open Category (category-unit A) using () renaming
      ( Object
        to BaseState
      ; Arrow
        to BaseStateArrow
      ; identity
        to base-state-identity
      ; compose
        to base-state-compose
      ; precompose
        to base-state-precompose
      ; postcompose
        to base-state-postcompose
      ; associative
        to base-state-associative
      )

    open SimpleBaseEditor e using () renaming
      ( StatePath
        to BaseStatePath
      )

    open SimpleChildEditor e' public
      hiding (update)

    update
      : (s : BaseState)
      → (sp : BaseStatePath s)
      → Result s sp
      → s' ∈ BaseState
        × sp' ∈ BaseStatePath s'
        × BaseStateArrow s s'
    update s sp r
      with SimpleChildEditor.update e' s sp r
    ... | (s' , sp')
      = (s' , sp' , CategoryUnit.arrow)

  child-editor-from-simple
    : SimpleChildEditor W F e
    → ChildEditor W F
      (base-editor-from-simple e)
  child-editor-from-simple e'
    = record {ChildEditorFromSimple e'}

