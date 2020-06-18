module Prover.Editor.Indexed where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀)
open import Prover.Category.Indexed.Base
  using (IndexedSet)
open import Prover.Category.Indexed.Partial.Base
  using (IndexedPartialFunction)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory; indexed-simple-category₀)
open import Prover.Category.Indexed.Simple.Convert
  using (indexed-category-simple)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor; indexed-split-functor₀)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Editor
  using (Editor; EventStack; SimpleEditor; SplitEditor; ViewStack;
    simple-editor)
open import Prover.Prelude

-- ## IndexedEditor

-- ### Definition

data IndexedEditor
  (V : ViewStack)
  (E : EventStack)
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedCategory C
  → Set₁
  where

  empty
    : {C : ChainCategory zero}
    → {C' : IndexedCategory C}
    → Editor V E (indexed-category₀ C')
    → IndexedEditor V E C'

  sigma
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : IndexedCategory C}
    → ((x : Category.Object (ChainCategory.head C))
      → IndexedEditor V E (IndexedCategory.tail C' x))
    → IndexedEditor V E C'

-- ### Interface

indexed-editor₀
  : {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory zero}
  → {C' : IndexedCategory C}
  → IndexedEditor V E C'
  → Editor V E (indexed-category₀ C')
indexed-editor₀ (empty e)
  = e

indexed-editor-tail
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory (suc n)}
  → {C' : IndexedCategory C}
  → IndexedEditor V E C'
  → (x : Category.Object (ChainCategory.head C))
  → IndexedEditor V E (IndexedCategory.tail C' x)
indexed-editor-tail (sigma e)
  = e

-- ## IndexedSimpleEditor

-- ### Definition

data IndexedSimpleEditor
  (V : ViewStack)
  (E : EventStack)
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → Set₁
  where

  empty
    : {C : ChainCategory zero}
    → {A : IndexedSimpleCategory C}
    → SimpleEditor V E (indexed-simple-category₀ A)
    → IndexedSimpleEditor V E A

  sigma
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {A : IndexedSimpleCategory C}
    → ((x : Category.Object (ChainCategory.head C))
      → IndexedSimpleEditor V E (IndexedSimpleCategory.tail A x))
    → IndexedSimpleEditor V E A

-- ### Interface

indexed-simple-editor₀
  : {V : ViewStack}
  → {E : EventStack}
  → {C : ChainCategory zero}
  → {A : IndexedSimpleCategory C}
  → IndexedSimpleEditor V E A
  → SimpleEditor V E (indexed-simple-category₀ A)
indexed-simple-editor₀ (empty e)
  = e

indexed-simple-editor-tail
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory (suc n)}
  → {A : IndexedSimpleCategory C}
  → IndexedSimpleEditor V E A
  → (x : Category.Object (ChainCategory.head C))
  → IndexedSimpleEditor V E (IndexedSimpleCategory.tail A x)
indexed-simple-editor-tail (sigma e)
  = e

-- ### Conversion

indexed-editor-simple
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedCategory C}
  → IndexedEditor V E C'
  → IndexedSimpleEditor V E
    (indexed-category-simple C')
indexed-editor-simple {n = zero} e
  = empty (simple-editor (indexed-editor₀ e))
indexed-editor-simple {n = suc _} e
  = sigma (λ x → indexed-editor-simple (indexed-editor-tail e x))

-- ## IndexedPartialEditor

record IndexedPartialEditor
  {n : ℕ}
  {C : ChainCategory n}
  (V : ViewStack)
  (E : EventStack)
  (C' : IndexedSet C)
  : Set₁
  where

  constructor

    indexed-partial-editor

  field
  
    {State}
      : IndexedSimpleCategory C

    indexed-simple-editor
      : IndexedSimpleEditor V E State

    indexed-partial-function
      : IndexedPartialFunction State C'

-- ## IndexedSplitEditor

-- ### Definition

record IndexedSplitEditor
  {n : ℕ}
  {C : ChainCategory n}
  (V : ViewStack)
  (E : EventStack)
  (C' : IndexedCategory C)
  : Set₁
  where

  constructor

    indexed-split-editor

  field

    {StateCategory}
      : IndexedCategory C

    indexed-editor
      : IndexedEditor V E StateCategory

    indexed-split-functor
      : IndexedSplitFunctor StateCategory C'

-- ### Interface

-- #### Destruction

module _
  {V : ViewStack}
  {E : EventStack}
  {C : ChainCategory zero}
  {C' : IndexedCategory C}
  where

  module IndexedSplitEditor₀
    (e : IndexedSplitEditor V E C')
    where

    StateCategory
      : Category
    StateCategory
      = indexed-category₀
        (IndexedSplitEditor.StateCategory e)

    editor
      : Editor V E StateCategory
    editor
      = indexed-editor₀
        (IndexedSplitEditor.indexed-editor e)

    split-functor
      : SplitFunctor StateCategory (indexed-category₀ C')
    split-functor
      = indexed-split-functor₀
        (IndexedSplitEditor.indexed-split-functor e)

  indexed-split-editor₀
    : IndexedSplitEditor V E C'
    → SplitEditor V E (indexed-category₀ C')
  indexed-split-editor₀ e
    = record {IndexedSplitEditor₀ e}

-- #### Tail

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory (suc n)}
  {C' : IndexedCategory C}
  where

  module IndexedSplitEditorTail
    (e : IndexedSplitEditor V E C')
    (x : Category.Object (ChainCategory.head C))
    where

    StateCategory
      : IndexedCategory (ChainCategory.tail C x)
    StateCategory
      = IndexedCategory.tail
        (IndexedSplitEditor.StateCategory e) x

    indexed-editor
      : IndexedEditor V E StateCategory
    indexed-editor
      = indexed-editor-tail
        (IndexedSplitEditor.indexed-editor e) x

    indexed-split-functor
      : IndexedSplitFunctor StateCategory (IndexedCategory.tail C' x)
    indexed-split-functor
      = IndexedSplitFunctor.tail
        (IndexedSplitEditor.indexed-split-functor e) x

  indexed-split-editor-tail
    : IndexedSplitEditor V E C'
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSplitEditor V E (IndexedCategory.tail C' x)
  indexed-split-editor-tail e x
    = record {IndexedSplitEditorTail e x}

