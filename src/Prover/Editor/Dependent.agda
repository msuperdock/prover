module Prover.Editor.Dependent where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory; dependent-category₀)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; dependent-simple-category₀)
open import Prover.Category.Dependent.Simple.Convert
  using (dependent-category-simple)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; dependent-split-functor₀)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Editor
  using (Editor; EventStack; SimpleEditor; SplitEditor; ViewStack; any)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Function.Dependent.Simple.Partial
  using (DependentSimplePartialFunction)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction)
open import Prover.Function.Dependent.Simple.Split
  using (DependentSimpleSplitFunction)
open import Prover.Prelude

-- ## DependentEditor

-- ### Definition

data DependentEditor
  (V : ViewStack)
  (E : EventStack)
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → Set₁
  where

  nil
    : {C : ChainCategory zero}
    → {C' : DependentCategory C}
    → Editor V E (dependent-category₀ C')
    → DependentEditor V E C'

  cons
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → ((x : Category.Object (ChainCategory.head C))
      → DependentEditor V E (DependentCategory.tail C' x))
    → DependentEditor V E C'

-- ### Interface

dependent-editor₀
  : {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory zero}
  → {C' : DependentCategory C}
  → DependentEditor V E C'
  → Editor V E (dependent-category₀ C')
dependent-editor₀ (nil e)
  = e

dependent-editor-tail
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory (suc n)}
  → {C' : DependentCategory C}
  → DependentEditor V E C'
  → (x : Category.Object (ChainCategory.head C))
  → DependentEditor V E (DependentCategory.tail C' x)
dependent-editor-tail (cons e)
  = e

-- ## DependentSimpleEditor

-- ### Definition

data DependentSimpleEditor
  (V : ViewStack)
  (E : EventStack)
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → Set₁
  where

  nil
    : {C : ChainCategory zero}
    → {A : DependentSimpleCategory C}
    → SimpleEditor V E (dependent-simple-category₀ A)
    → DependentSimpleEditor V E A

  cons
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {A : DependentSimpleCategory C}
    → ((x : Category.Object (ChainCategory.head C))
      → DependentSimpleEditor V E (DependentSimpleCategory.tail A x))
    → DependentSimpleEditor V E A

-- ### Interface

dependent-simple-editor₀
  : {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory zero}
  → {A : DependentSimpleCategory C}
  → DependentSimpleEditor V E A
  → SimpleEditor V E (dependent-simple-category₀ A)
dependent-simple-editor₀ (nil e)
  = e

dependent-simple-editor-tail
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory (suc n)}
  → {A : DependentSimpleCategory C}
  → DependentSimpleEditor V E A
  → (x : Category.Object (ChainCategory.head C))
  → DependentSimpleEditor V E (DependentSimpleCategory.tail A x)
dependent-simple-editor-tail (cons e)
  = e

-- ### Conversion

dependent-editor-simple
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentEditor V E C'
  → DependentSimpleEditor V E
    (dependent-category-simple C')
dependent-editor-simple
  {n = zero} e
  = nil
    (any
      (dependent-editor₀ e))
dependent-editor-simple
  {n = suc _} e
  = cons
    (λ x → dependent-editor-simple
      (dependent-editor-tail e x))

-- ## DependentPartialEditor

record DependentPartialEditor
  {n : ℕ}
  {C : ChainCategory n}
  (V : ViewStack)
  (E : EventStack)
  (C' : DependentSet C)
  : Set₁
  where

  field
  
    StateSimpleCategory
      : DependentSimpleCategory C

    dependent-simple-editor
      : DependentSimpleEditor V E StateSimpleCategory

    dependent-simple-partial-function
      : DependentSimplePartialFunction StateSimpleCategory C'

-- ## DependentSplitEditor

-- ### Definition

record DependentSplitEditor
  {n : ℕ}
  {C : ChainCategory n}
  (V : ViewStack)
  (E : EventStack)
  (C' : DependentCategory C)
  : Set₁
  where

  field

    StateCategory
      : DependentCategory C

    dependent-editor
      : DependentEditor V E StateCategory

    dependent-split-functor
      : DependentSplitFunctor StateCategory C'

-- ### Interface

-- #### Destruction

module _
  {V : ViewStack}
  {E : EventStack}
  {C : ChainCategory zero}
  {C' : DependentCategory C}
  where

  module DependentSplitEditor₀
    (e : DependentSplitEditor V E C')
    where

    StateCategory
      : Category
    StateCategory
      = dependent-category₀
        (DependentSplitEditor.StateCategory e)

    editor
      : Editor V E StateCategory
    editor
      = dependent-editor₀
        (DependentSplitEditor.dependent-editor e)

    split-functor
      : SplitFunctor StateCategory (dependent-category₀ C')
    split-functor
      = dependent-split-functor₀
        (DependentSplitEditor.dependent-split-functor e)

  dependent-split-editor₀
    : DependentSplitEditor V E C'
    → SplitEditor V E (dependent-category₀ C')
  dependent-split-editor₀ e
    = record {DependentSplitEditor₀ e}

-- #### Tail

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory (suc n)}
  {C' : DependentCategory C}
  where

  module DependentSplitEditorTail
    (e : DependentSplitEditor V E C')
    (x : Category.Object (ChainCategory.head C))
    where

    StateCategory
      : DependentCategory (ChainCategory.tail C x)
    StateCategory
      = DependentCategory.tail
        (DependentSplitEditor.StateCategory e) x

    dependent-editor
      : DependentEditor V E StateCategory
    dependent-editor
      = dependent-editor-tail
        (DependentSplitEditor.dependent-editor e) x

    dependent-split-functor
      : DependentSplitFunctor StateCategory (DependentCategory.tail C' x)
    dependent-split-functor
      = DependentSplitFunctor.tail
        (DependentSplitEditor.dependent-split-functor e) x

  dependent-split-editor-tail
    : DependentSplitEditor V E C'
    → (x : Category.Object (ChainCategory.head C))
    → DependentSplitEditor V E (DependentCategory.tail C' x)
  dependent-split-editor-tail e x
    = record {DependentSplitEditorTail e x}

-- ## DependentMainEditor

record DependentMainEditor
  {n : ℕ}
  (V : ViewStack)
  (E : EventStack)
  (S : Set)
  (C : ChainCategory n)
  : Set₁
  where

  field

    StateSimpleCategory
      : DependentSimpleCategory C

    dependent-simple-editor
      : DependentSimpleEditor V E StateSimpleCategory

    dependent-simple-split-function
      : DependentSimpleSplitFunction S StateSimpleCategory

    dependent-simple-bool-function
      : DependentSimpleBoolFunction StateSimpleCategory

-- ## DependentSplitMainEditor

-- ### Definition

record DependentSplitMainEditor
  {n : ℕ}
  {C : ChainCategory n}
  (V : ViewStack)
  (E : EventStack)
  (S : Set)
  (P : Set)
  (C' : DependentCategory C)
  : Set₁
  where

  field

    StateCategory
      : DependentCategory C

    dependent-editor
      : DependentEditor V E StateCategory

    state-dependent-split-function
      : DependentSplitFunction S StateCategory

    pure-dependent-split-function
      : DependentSplitFunction P C'

    dependent-split-functor
      : DependentSplitFunctor StateCategory C'

-- ### Conversion

dependent-split-main-editor-unmain
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentSplitMainEditor V E S P C'
  → DependentSplitEditor V E C'
dependent-split-main-editor-unmain e
  = record {DependentSplitMainEditor e}

