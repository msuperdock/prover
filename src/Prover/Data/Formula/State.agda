module Prover.Data.Formula.State where

open import Category.Simple.Split
  using (SimpleSplitFunctor)

open import Prover.Data.Any
  using (Any; any)
open import Prover.Data.Bool
  using (Bool; T; false; true)
open import Prover.Data.Empty
  using (⊥-elim)
open import Prover.Data.Equal
  using (_≡_; refl; sub)
open import Prover.Data.Fin
  using (Fin; suc; zero)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Formula.Construct
  using (Construct)
open import Prover.Data.Function
  using (id)
open import Prover.Data.Inspect
  using ([_]; inspect)
open import Prover.Data.Maybe
  using (Maybe; just; maybe; nothing)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Nat
  using (ℕ; suc; zero)
open import Prover.Data.Relation
  using (no; yes)
open import Prover.Data.Symbol
  using (Symbol; both; left; neither; right; symbol)
open import Prover.Data.Symbols
  using (Symbols; sym_∈_)
open import Prover.Data.Variable
  using (Variable)
open import Prover.Data.Variables
  using (Variables; var_∈_)
open import Prover.Data.Vec
  using (Vec; []; _∷_; _!_)

-- ## Internal

module Internal where

  -- ### Definitions
  
  -- #### Types

  data FormulaState
    (ss : Symbols)
    (vs : Variables)
    : Bool
    → Set
  
  data SandboxState
    (ss : Symbols)
    (vs : Variables)
    (m : Bool)
    : ℕ
    → Set
  
  data Left
    (ss : Symbols)
    (vs : Variables)
    (m : Bool)
    (s : Symbol)
    : Set
  
  data Right
    (ss : Symbols)
    (vs : Variables)
    (m : Bool)
    (s : Symbol)
    : Set
  
  formula-state-construct
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → FormulaState ss vs m
    → Construct
  
  formula-state-left-closed
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → FormulaState ss vs m
    → Bool
  
  FormulaStateLeftClosed
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → FormulaState ss vs m
    → Set
  
  formula-state-right-closed
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → FormulaState ss vs m
    → Bool
  
  FormulaStateRightClosed
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → FormulaState ss vs m
    → Set
  
  sandbox-state-head
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → Any (SandboxState ss vs m)
    → FormulaState ss vs m
  
  sandbox-state-length
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → Any (SandboxState ss vs m)
    → ℕ
  
  data FormulaState ss vs where
  
    hole
      : {m : Bool}
      → FormulaState ss vs m
  
    parens
      : {m : Bool}
      → Any (SandboxState ss vs m)
      → FormulaState ss vs m
  
    meta
      : Meta
      → FormulaState ss vs true
  
    variable'
      : {m : Bool}
      → (v : Variable)
      → .(var v ∈ vs)
      → FormulaState ss vs m
  
    symbol
      : {m : Bool}
      → (s : Symbol)
      → .(sym s ∈ ss)
      → Left ss vs m s
      → Right ss vs m s
      → Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s)
      → FormulaState ss vs m
  
  data SandboxState ss vs m where
  
    singleton
      : FormulaState ss vs m
      → SandboxState ss vs m (suc zero)
  
    cons
      : (f : FormulaState ss vs m)
      → FormulaStateRightClosed f
      → (s : Any (SandboxState ss vs m))
      → FormulaStateLeftClosed (sandbox-state-head s)
      → SandboxState ss vs m (suc (sandbox-state-length s))
  
  data Left ss vs m s where
  
    nothing
      : Symbol.¬HasLeft s
      → Left ss vs m s
  
    just
      : (f : FormulaState ss vs m)
      → Construct.LeftValid s (formula-state-construct f)
      → Left ss vs m s
  
  data Right ss vs m s where
  
    nothing
      : Symbol.¬HasRight s
      → Right ss vs m s
  
    just
      : (f : FormulaState ss vs m)
      → Construct.RightValid s (formula-state-construct f)
      → Right ss vs m s
  
  formula-state-construct hole
    = Construct.atom
  formula-state-construct (parens _)
    = Construct.atom
  formula-state-construct (meta _)
    = Construct.atom
  formula-state-construct (variable' _ _)
    = Construct.atom
  formula-state-construct (symbol s _ _ _ _)
    = Construct.symbol s
  
  sandbox-state-head (any (singleton f))
    = f
  sandbox-state-head (any (cons f _ _ _))
    = f
  
  sandbox-state-length (any {n} _)
    = n
  
  formula-state-left-closed hole
    = false
  formula-state-left-closed (parens _)
    = true
  formula-state-left-closed (meta _)
    = true
  formula-state-left-closed (variable' _ _)
    = true
  formula-state-left-closed (symbol _ _ (nothing _) _ _)
    = true
  formula-state-left-closed (symbol _ _ (just f _) _ _)
    = formula-state-left-closed f
  
  FormulaStateLeftClosed f
    = T (formula-state-left-closed f)
  
  formula-state-right-closed hole
    = false
  formula-state-right-closed (parens _)
    = true
  formula-state-right-closed (meta _)
    = true
  formula-state-right-closed (variable' _ _)
    = true
  formula-state-right-closed (symbol _ _ _ (nothing _) _)
    = true
  formula-state-right-closed (symbol _ _ _ (just f _) _)
    = formula-state-right-closed f
  
  FormulaStateRightClosed f
    = T (formula-state-right-closed f)
  
  sandbox-state-left-closed
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → Any (SandboxState ss vs m)
    → Bool
  sandbox-state-left-closed s
    = formula-state-left-closed (sandbox-state-head s)
  
  SandboxStateLeftClosed
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → Any (SandboxState ss vs m)
    → Set
  SandboxStateLeftClosed s
    = T (sandbox-state-left-closed s)
  
  formula-state-center-arity
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → FormulaState ss vs m
    → ℕ
  formula-state-center-arity hole
    = zero
  formula-state-center-arity (parens _)
    = suc (zero)
  formula-state-center-arity (meta _)
    = zero
  formula-state-center-arity (variable' _ _)
    = zero
  formula-state-center-arity (symbol s _ _ _ _)
    = Symbol.center-arity s
  
  formula-state-center
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → (f : FormulaState ss vs m)
    → Vec (Any (SandboxState ss vs m)) (formula-state-center-arity f)
  formula-state-center hole
    = []
  formula-state-center (parens s)
    = s ∷ []
  formula-state-center (meta _)
    = []
  formula-state-center (variable' _ _)
    = []
  formula-state-center (symbol _ _ _ _ ss)
    = ss
  
  sandbox-state-lookup
    : {ss : Symbols}
    → {vs : Variables}
    → {m : Bool}
    → (s : Any (SandboxState ss vs m))
    → Fin (sandbox-state-length s)
    → FormulaState ss vs m
  sandbox-state-lookup (any (singleton f)) zero
    = f
  sandbox-state-lookup (any (cons f _ _ _)) zero
    = f
  sandbox-state-lookup (any (cons _ _ s _)) (suc k)
    = sandbox-state-lookup s k
  
  -- #### Paths

  module _
    {ss : Symbols}
    {vs : Variables}
    {m : Bool}
    where
  
    data FormulaStatePath
      : FormulaState ss vs m
      → Set
  
    data SandboxStatePath
      (s : Any (SandboxState ss vs m))
      : Set
  
    data FormulaStatePath where
  
      stop
        : {f : FormulaState ss vs m}
        → FormulaStatePath f
  
      left
        : {s : Symbol}
        → .{p : sym s ∈ ss}
        → {f : FormulaState ss vs m}
        → {lv : Construct.LeftValid s (formula-state-construct f)}
        → {r : Right ss vs m s}
        → {cs : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s)}
        → FormulaStatePath f
        → FormulaStatePath (symbol s p (just f lv) r cs)

      right
        : {s : Symbol}
        → .{p : sym s ∈ ss}
        → {l : Left ss vs m s}
        → {f : FormulaState ss vs m}
        → {rv : Construct.RightValid s (formula-state-construct f)}
        → {cs : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s)}
        → FormulaStatePath f
        → FormulaStatePath (symbol s p l (just f rv) cs)
  
      center
        : {f : FormulaState ss vs m}
        → (k : Fin (formula-state-center-arity f))
        → SandboxStatePath (formula-state-center f ! k)
        → FormulaStatePath f

    data SandboxStatePath s where
  
      end
        : SandboxStatePath s
  
      go
        : (k : Fin (sandbox-state-length s))
        → FormulaStatePath (sandbox-state-lookup s k)
        → SandboxStatePath s

  -- ### Interface
  
  module _
    {ss : Symbols}
    {vs : Variables}
    {m : Bool}
    where
  
    -- #### Types

    data FormulaStateHasLeft
      : FormulaState ss vs m
      → Set
      where

      tt
        : {s : Symbol}
        → .{p : sym s ∈ ss}
        → {f : FormulaState ss vs m}
        → {lv : Construct.LeftValid s (formula-state-construct f)}
        → {r : Right ss vs m s}
        → {cs : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s)}
        → FormulaStateHasLeft (symbol s p (just f lv) r cs)

    data FormulaStateHasRight
      : FormulaState ss vs m
      → Set
      where

      tt
        : {s : Symbol}
        → .{p : sym s ∈ ss}
        → {l : Left ss vs m s}
        → {f : FormulaState ss vs m}
        → {rv : Construct.RightValid s (formula-state-construct f)}
        → {cs : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s)}
        → FormulaStateHasRight (symbol s p l (just f rv) cs)

    formula-state-left
      : (f : FormulaState ss vs m)
      → FormulaStateHasLeft f
      → FormulaState ss vs m
    formula-state-left _ (tt {f = f})
      = f

    formula-state-right
      : (f : FormulaState ss vs m)
      → FormulaStateHasRight f
      → FormulaState ss vs m
    formula-state-right _ (tt {f = f})
      = f

    -- #### Paths

    formula-state-path-not-left
      : {f : FormulaState ss vs m}
      → FormulaStatePath f
      → Bool
    formula-state-path-not-left (left _)
      = false
    formula-state-path-not-left _
      = true

    FormulaStatePathNotLeft
      : {f : FormulaState ss vs m}
      → FormulaStatePath f
      → Set
    FormulaStatePathNotLeft f
      = T (formula-state-path-not-left f)

    formula-state-path-not-right
      : {f : FormulaState ss vs m}
      → FormulaStatePath f
      → Bool
    formula-state-path-not-right (right _)
      = false
    formula-state-path-not-right _
      = true

    FormulaStatePathNotRight
      : {f : FormulaState ss vs m}
      → FormulaStatePath f
      → Set
    FormulaStatePathNotRight f
      = T (formula-state-path-not-right f)

    formula-state-path-leftmost
      : (f : FormulaState ss vs m)
      → FormulaStatePath f
    formula-state-path-leftmost hole
      = stop
    formula-state-path-leftmost (parens _)
      = stop
    formula-state-path-leftmost (meta _)
      = stop
    formula-state-path-leftmost (variable' _ _)
      = stop
    formula-state-path-leftmost (symbol _ _ (nothing _) _ _)
      = stop
    formula-state-path-leftmost (symbol _ _ (just f _) _ _)
      = left (formula-state-path-leftmost f)
  
    formula-state-path-rightmost
      : (f : FormulaState ss vs m)
      → FormulaStatePath f
    formula-state-path-rightmost hole
      = stop
    formula-state-path-rightmost (parens _)
      = stop
    formula-state-path-rightmost (meta _)
      = stop
    formula-state-path-rightmost (variable' _ _)
      = stop
    formula-state-path-rightmost (symbol _ _ _ (nothing _) _)
      = stop
    formula-state-path-rightmost (symbol _ _ _ (just f _) _)
      = right (formula-state-path-rightmost f)

    sandbox-state-path-leftmost
      : (s : Any (SandboxState ss vs m))
      → SandboxStatePath s
    sandbox-state-path-leftmost (any (singleton f))
      = go zero (formula-state-path-leftmost f)
    sandbox-state-path-leftmost (any (cons f _ _ _))
      = go zero (formula-state-path-leftmost f)
  
    formula-state-path-left
      : {f : FormulaState ss vs m}
      → FormulaStatePath f
      → Maybe (FormulaStatePath f)

    sandbox-state-path-left
      : {s : Any (SandboxState ss vs m)}
      → SandboxStatePath s
      → Maybe (SandboxStatePath s)

    formula-state-path-left {f = hole} stop
      = nothing
    formula-state-path-left {f = meta _} stop
      = nothing
    formula-state-path-left {f = variable' _ _} stop
      = nothing
    formula-state-path-left {f = parens _} stop
      = nothing
    formula-state-path-left {f = symbol _ _ (nothing _) _ _} stop
      = nothing
    formula-state-path-left {f = symbol _ _ (just f _) _ _} stop
      = just (left (formula-state-path-rightmost f))

    formula-state-path-left (left fp)
      with formula-state-path-left fp
    ... | nothing
      = nothing
    ... | just fp'
      = just (left fp')

    formula-state-path-left (right fp)
      with formula-state-path-left fp
    formula-state-path-left {f = symbol _ _ _ _ []} _ | nothing
      = just stop
    formula-state-path-left {f = symbol _ _ _ _ (_ ∷ cs)} _ | nothing
      = just (center (Fin.maximum (Vec.length cs)) end)
    ... | just fp'
      = just (right fp')

    formula-state-path-left (center k sp)
      with sandbox-state-path-left sp
      | Fin.decrement k
    ... | nothing | nothing
      = just stop
    ... | nothing | just k'
      = just (center k' end)
    ... | just sp' | _
      = just (center k sp')

    sandbox-state-path-left {s = any (singleton f)} end
      = just (go zero
        (formula-state-path-rightmost f))
    sandbox-state-path-left {s = s@(any {suc n} (cons _ _ _ _))} end
      = just (go (Fin.maximum n)
        (formula-state-path-rightmost (sandbox-state-lookup s (Fin.maximum n))))
    sandbox-state-path-left {s = s} (go k fp)
      with formula-state-path-left fp
      | Fin.decrement k
    ... | nothing | nothing
      = nothing
    ... | nothing | just k'
      = just (go k' (formula-state-path-rightmost
        (sandbox-state-lookup s k')))
    ... | just fp' | _
      = just (go k fp')

    formula-state-path-right
      : {f : FormulaState ss vs m}
      → FormulaStatePath f
      → Maybe (FormulaStatePath f)
  
    sandbox-state-path-right
      : {s : Any (SandboxState ss vs m)}
      → SandboxStatePath s
      → Maybe (SandboxStatePath s)
  
    formula-state-path-right {f = hole} stop
      = nothing
    formula-state-path-right {f = meta _} stop
      = nothing
    formula-state-path-right {f = variable' _ _} stop
      = nothing
    formula-state-path-right {f = parens s} stop
      = just (center zero (sandbox-state-path-leftmost s))
    formula-state-path-right {f = symbol _ _ _ (nothing _) []} stop
      = nothing
    formula-state-path-right {f = symbol _ _ _ (just f _) []} stop
      = just (right (formula-state-path-leftmost f))
    formula-state-path-right {f = symbol _ _ _ _ (s ∷ _)} stop
      = just (center zero (sandbox-state-path-leftmost s))

    formula-state-path-right (left fp)
      with formula-state-path-right fp
    ... | nothing
      = just stop
    ... | just fp'
      = just (left fp')

    formula-state-path-right (right fp)
      with formula-state-path-right fp
    ... | nothing
      = nothing
    ... | just fp'
      = just (right fp')
  
    formula-state-path-right (center k sp)
      with sandbox-state-path-right sp
      | Fin.increment k 
      | inspect Fin.increment k
    formula-state-path-right {f = parens _} _
      | nothing | nothing | _
      = nothing
    formula-state-path-right {f = symbol _ _ _ (nothing _) _} _
      | nothing | nothing | _
      = nothing
    formula-state-path-right {f = symbol _ _ _ (just f _) _} _
      | nothing | nothing | _
      = just (right (formula-state-path-leftmost f))
    formula-state-path-right {f = parens _} (center zero _)
      | nothing | just _ | [ p ]
      = ⊥-elim (Maybe.nothing≢just p)
    formula-state-path-right {f = symbol _ _ _ _ ss'} _
      | nothing | just k' | _
      = just (center k' (sandbox-state-path-leftmost (ss' ! k')))
    ... | just sp' | _ | _
      = just (center k sp')
  
    sandbox-state-path-right end
      = nothing
    sandbox-state-path-right {s = s} (go k fp)
      with formula-state-path-right fp
      | Fin.increment k
    ... | nothing | nothing
      = just end
    ... | nothing | just k'
      = just (go k' (formula-state-path-leftmost
        (sandbox-state-lookup s k')))
    ... | just fp' | _
      = just (go k fp')
  
    sandbox-state-path-right-def
      : {s : Any (SandboxState ss vs m)}
      → SandboxStatePath s
      → SandboxStatePath s
    sandbox-state-path-right-def sp
      = maybe (sandbox-state-path-right sp) sp id
  
    formula-state-path-left-leftmost
      : (f : FormulaState ss vs m)
      → formula-state-path-left (formula-state-path-leftmost f) ≡ nothing
    formula-state-path-left-leftmost hole
      = refl
    formula-state-path-left-leftmost (parens _)
      = refl
    formula-state-path-left-leftmost (meta _)
      = refl
    formula-state-path-left-leftmost (variable' _ _)
      = refl
    formula-state-path-left-leftmost (symbol _ _ (nothing _) _ _)
      = refl
    formula-state-path-left-leftmost (symbol _ _ (just f _) _ _)
      with formula-state-path-left (formula-state-path-leftmost f)
      | formula-state-path-left-leftmost f
    ... | _ | refl
      = refl

    sandbox-state-path-left-leftmost
      : (s : Any (SandboxState ss vs m))
      → sandbox-state-path-left (sandbox-state-path-leftmost s) ≡ nothing
    sandbox-state-path-left-leftmost (any (singleton f))
      with formula-state-path-left (formula-state-path-leftmost f)
      | formula-state-path-left-leftmost f
    ... | _ | refl
      = refl
    sandbox-state-path-left-leftmost (any (cons f _ _ _))
      with formula-state-path-left (formula-state-path-leftmost f)
      | formula-state-path-left-leftmost f
    ... | _ | refl
      = refl

    sandbox-state-path-cons
      : {f : FormulaState ss vs m}
      → {rc : FormulaStateRightClosed f}
      → {s : Any (SandboxState ss vs m)}
      → {lc : SandboxStateLeftClosed s}
      → SandboxStatePath s
      → SandboxStatePath (any (cons f rc s lc))
    sandbox-state-path-cons end
      = end
    sandbox-state-path-cons (go k path)
      = go (suc k) path

  -- ### Construction
  
  module _
    {ss : Symbols}
    {vs : Variables}
    {m : Bool}
    where
  
    sandbox-state-hole
      : Any (SandboxState ss vs m)
    sandbox-state-hole
      = any (singleton hole)

    sandbox-state-holes
      : {n : ℕ}
      → Vec (Any (SandboxState ss vs m)) n
    sandbox-state-holes {zero}
      = []
    sandbox-state-holes {suc _}
      = sandbox-state-hole ∷ sandbox-state-holes

    left-hole
      : {s : Symbol}
      → Left ss vs m s
    left-hole {s = symbol {has-left = false} _ _ _ _ _}
      = nothing Symbol.tt
    left-hole {s = symbol {has-left = true} _ _ _ _ _}
      = just hole (Construct.left-valid Symbol.tt refl)

    right-hole
      : {s : Symbol}
      → Right ss vs m s
    right-hole {s = symbol {has-right = false} _ _ _ _ _}
      = nothing Symbol.tt
    right-hole {s = symbol {has-right = true} _ _ _ _ _}
      = just hole (Construct.right-valid Symbol.tt refl)

    left-force
      : {s : Symbol}
      → Symbol.HasLeft s
      → FormulaState ss vs m
      → Left ss vs m s
    left-force {s = s} hl f
      with Construct.left-valid? s (formula-state-construct f)
    ... | no _
      = just (parens (any (singleton f))) (Construct.left-valid hl refl)
    ... | yes lv
      = just f lv
  
    right-force
      : {s : Symbol}
      → Symbol.HasRight s
      → FormulaState ss vs m
      → Right ss vs m s
    right-force {s = s} hr f
      with Construct.right-valid? s (formula-state-construct f)
    ... | no _
      = just (parens (any (singleton f))) (Construct.right-valid hr refl)
    ... | yes rv
      = just f rv

    parens-template
      : Any (SandboxState ss vs m)
    parens-template
      = any (singleton (parens sandbox-state-hole))

    variable-template
      : (v : Variable)
      → var v ∈ vs
      → Any (SandboxState ss vs m)
    variable-template v p
      = any (singleton (variable' v p))

    symbol-template
      : (s : Symbol)
      → sym s ∈ ss
      → Any (SandboxState ss vs m)
    symbol-template s p
      = any (singleton (symbol s p left-hole right-hole sandbox-state-holes))
  
  -- ### Conversion
  
  -- #### To
  
  module _
    {ss : Symbols}
    {vs : Variables}
    {m : Bool}
    where
  
    formula-state-to-formula
      : FormulaState ss vs m
      → Maybe (Formula ss vs m)
  
    sandbox-state-to-formula
      : Any (SandboxState ss vs m)
      → Maybe (Formula ss vs m)
  
    sandbox-state-to-formulas
      : {n : ℕ}
      → Vec (Any (SandboxState ss vs m)) n
      → Maybe (Vec (Formula ss vs m) n)
  
    formula-state-to-formula hole
      = nothing
    formula-state-to-formula (parens s)
      = sandbox-state-to-formula s
    formula-state-to-formula (meta m)
      = just (Formula.meta m)
    formula-state-to-formula (variable' v p)
      = just (Formula.variable' v p)
  
    formula-state-to-formula
      (symbol s@(symbol neither _ _ _ _) p _ _ cs)
      with sandbox-state-to-formulas cs
    ... | nothing
      = nothing
    ... | just fs
      = just (Formula.symbol s p fs)

    formula-state-to-formula
      (symbol s@(symbol left _ _ _ _) p (just l _) _ cs)
      with formula-state-to-formula l
      | sandbox-state-to-formulas cs
    ... | nothing | _
      = nothing
    ... | _ | nothing
      = nothing
    ... | just f | just fs
      = just (Formula.symbol s p (f ∷ fs))

    formula-state-to-formula
      (symbol s@(symbol right _ _ _ _) p _ (just r _) cs)
      with formula-state-to-formula r
      | sandbox-state-to-formulas cs
    ... | nothing | _
      = nothing
    ... | _ | nothing
      = nothing
    ... | just f | just fs
      = just (Formula.symbol s p (Vec.snoc fs f))

    formula-state-to-formula
      (symbol s@(symbol both _ _ _ _) p (just l _) (just r _) cs)
      with formula-state-to-formula l
      | formula-state-to-formula r
      | sandbox-state-to-formulas cs
    ... | nothing | _ | _
      = nothing
    ... | _ | nothing | _
      = nothing
    ... | _ | _ | nothing
      = nothing
    ... | just f | just f' | just fs
      = just (Formula.symbol s p (f ∷ Vec.snoc fs f'))

    sandbox-state-to-formula (any (singleton f))
      = formula-state-to-formula f
    sandbox-state-to-formula (any (cons _ _ _ _))
      = nothing
  
    sandbox-state-to-formulas []
      = just []
    sandbox-state-to-formulas (s ∷ ss')
      with sandbox-state-to-formula s
      | sandbox-state-to-formulas ss'
    ... | nothing | _
      = nothing
    ... | _ | nothing
      = nothing
    ... | just f | just fs
      = just (f ∷ fs)
  
  -- #### From
  
  module _
    {ss : Symbols}
    {vs : Variables}
    {m : Bool}
    where
  
    formula-state-from-formula
      : Formula ss vs m
      → FormulaState ss vs m
  
    formula-state-from-formulas-last
      : {n : ℕ}
      → Vec (Formula ss vs m) (suc n)
      → FormulaState ss vs m
  
    sandbox-state-from-formula
      : Formula ss vs m
      → Any (SandboxState ss vs m)
  
    sandbox-state-from-formulas
      : {n : ℕ}
      → Vec (Formula ss vs m) n
      → Vec (Any (SandboxState ss vs m)) n
  
    sandbox-state-from-formulas-init
      : {n : ℕ}
      → Vec (Formula ss vs m) (suc n)
      → Vec (Any (SandboxState ss vs m)) n
  
    formula-state-from-formula (Formula.meta m)
      = meta m
    formula-state-from-formula (Formula.variable' v p)
      = variable' v p
  
    formula-state-from-formula
      (Formula.symbol s@(symbol neither _ _ _ _) p fs)
      = symbol s p
        (nothing Symbol.tt)
        (nothing Symbol.tt)
        (sandbox-state-from-formulas fs)

    formula-state-from-formula
      (Formula.symbol s@(symbol left _ _ _ _) p (f ∷ fs))
      = symbol s p
        (left-force Symbol.tt (formula-state-from-formula f))
        (nothing Symbol.tt)
        (sandbox-state-from-formulas fs)
  
    formula-state-from-formula
      (Formula.symbol s@(symbol right _ _ _ _) p fs)
      = symbol s p
        (nothing Symbol.tt)
        (right-force Symbol.tt (formula-state-from-formulas-last fs))
        (sandbox-state-from-formulas-init fs)
  
    formula-state-from-formula
      (Formula.symbol s@(symbol both _ _ _ _) p (f ∷ fs))
      = symbol s p
        (left-force Symbol.tt (formula-state-from-formula f))
        (right-force Symbol.tt (formula-state-from-formulas-last fs))
        (sandbox-state-from-formulas-init fs)
  
    formula-state-from-formulas-last (f ∷ [])
      = formula-state-from-formula f
    formula-state-from-formulas-last (_ ∷ fs@(_ ∷ _))
      = formula-state-from-formulas-last fs
  
    sandbox-state-from-formula f
      = any (singleton (formula-state-from-formula f))
  
    sandbox-state-from-formulas []
      = []
    sandbox-state-from-formulas (f ∷ fs)
      = sandbox-state-from-formula f ∷ sandbox-state-from-formulas fs
  
    sandbox-state-from-formulas-init (_ ∷ [])
      = []
    sandbox-state-from-formulas-init (f ∷ fs@(_ ∷ _))
      = sandbox-state-from-formula f ∷ sandbox-state-from-formulas-init fs
  
  -- #### Valid

  module _
    {ss : Symbols}
    {vs : Variables}
    {m : Bool}
    where
  
    formula-state-to-from-formula
      : (f : Formula ss vs m)
      → formula-state-to-formula (formula-state-from-formula f) ≡ just f

    formula-state-to-from-formulas-last
      : {n : ℕ}
      → (fs : Vec (Formula ss vs m) (suc n))
      → formula-state-to-formula (formula-state-from-formulas-last fs)
        ≡ just (Vec.last fs)

    sandbox-state-to-from-formula
      : (f : Formula ss vs m)
      → sandbox-state-to-formula (sandbox-state-from-formula f) ≡ just f

    sandbox-state-to-from-formulas
      : {n : ℕ}
      → (fs : Vec (Formula ss vs m) n)
      → sandbox-state-to-formulas (sandbox-state-from-formulas fs) ≡ just fs

    sandbox-state-to-from-formulas-init
      : {n : ℕ}
      → (fs : Vec (Formula ss vs m) (suc n))
      → sandbox-state-to-formulas (sandbox-state-from-formulas-init fs)
        ≡ just (Vec.init fs)

    formula-state-to-from-formula (Formula.meta _)
      = refl
    formula-state-to-from-formula (Formula.variable' _ _)
      = refl

    formula-state-to-from-formula
      (Formula.symbol (symbol neither _ _ _ _) _ fs)
      with sandbox-state-to-formulas (sandbox-state-from-formulas fs)
      | sandbox-state-to-from-formulas fs
    ... | _ | refl
      = refl

    formula-state-to-from-formula
      (Formula.symbol s@(symbol left _ _ _ _) _ (f ∷ _))
      with Construct.left-valid? s
        (formula-state-construct (formula-state-from-formula f))

    formula-state-to-from-formula
      (Formula.symbol (symbol left _ _ _ _) _ (f ∷ fs)) | no _
      with formula-state-to-formula (formula-state-from-formula f)
      | formula-state-to-from-formula f
      | sandbox-state-to-formulas (sandbox-state-from-formulas fs)
      | sandbox-state-to-from-formulas fs
    ... | _ | refl | _ | refl
      = refl

    formula-state-to-from-formula
      (Formula.symbol (symbol left _ _ _ _) _ (f ∷ fs)) | yes _
      with formula-state-to-formula (formula-state-from-formula f)
      | formula-state-to-from-formula f
      | sandbox-state-to-formulas (sandbox-state-from-formulas fs)
      | sandbox-state-to-from-formulas fs
    ... | _ | refl | _ | refl
      = refl

    formula-state-to-from-formula
      (Formula.symbol s@(symbol right _ _ _ _) _ fs)
      with Construct.right-valid? s
        (formula-state-construct (formula-state-from-formulas-last fs))

    formula-state-to-from-formula
      (Formula.symbol s@(symbol right _ _ _ _) p fs) | no _
      with formula-state-to-formula (formula-state-from-formulas-last fs)
      | formula-state-to-from-formulas-last fs
      | sandbox-state-to-formulas (sandbox-state-from-formulas-init fs)
      | sandbox-state-to-from-formulas-init fs
    ... | _ | refl | _ | refl
      = sub (λ fs' → just (Formula.symbol s p fs')) (Vec.snoc-init-last fs) 

    formula-state-to-from-formula
      (Formula.symbol s@(symbol right _ _ _ _) p fs) | yes _
      with formula-state-to-formula (formula-state-from-formulas-last fs)
      | formula-state-to-from-formulas-last fs
      | sandbox-state-to-formulas (sandbox-state-from-formulas-init fs)
      | sandbox-state-to-from-formulas-init fs
    ... | _ | refl | _ | refl
      = sub (λ fs' → just (Formula.symbol s p fs')) (Vec.snoc-init-last fs) 

    formula-state-to-from-formula
      (Formula.symbol s@(symbol both _ _ _ _) _ (f ∷ fs))
      with Construct.left-valid? s
        (formula-state-construct (formula-state-from-formula f))
      | Construct.right-valid? s
        (formula-state-construct (formula-state-from-formulas-last fs))

    formula-state-to-from-formula
      (Formula.symbol s@(symbol both _ _ _ _) p (f ∷ fs)) | no _ | no _
      with formula-state-to-formula (formula-state-from-formula f)
      | formula-state-to-from-formula f
      | formula-state-to-formula (formula-state-from-formulas-last fs)
      | formula-state-to-from-formulas-last fs
      | sandbox-state-to-formulas (sandbox-state-from-formulas-init fs)
      | sandbox-state-to-from-formulas-init fs
    ... | _ | refl | _ | refl | _ | refl
      = sub (λ fs' → just (Formula.symbol s p (f ∷ fs')))
        (Vec.snoc-init-last fs)

    formula-state-to-from-formula
      (Formula.symbol s@(symbol both _ _ _ _) p (f ∷ fs)) | no _ | yes _
      with formula-state-to-formula (formula-state-from-formula f)
      | formula-state-to-from-formula f
      | formula-state-to-formula (formula-state-from-formulas-last fs)
      | formula-state-to-from-formulas-last fs
      | sandbox-state-to-formulas (sandbox-state-from-formulas-init fs)
      | sandbox-state-to-from-formulas-init fs
    ... | _ | refl | _ | refl | _ | refl
      = sub (λ fs' → just (Formula.symbol s p (f ∷ fs')))
        (Vec.snoc-init-last fs)

    formula-state-to-from-formula
      (Formula.symbol s@(symbol both _ _ _ _) p (f ∷ fs)) | yes _ | no _
      with formula-state-to-formula (formula-state-from-formula f)
      | formula-state-to-from-formula f
      | formula-state-to-formula (formula-state-from-formulas-last fs)
      | formula-state-to-from-formulas-last fs
      | sandbox-state-to-formulas (sandbox-state-from-formulas-init fs)
      | sandbox-state-to-from-formulas-init fs
    ... | _ | refl | _ | refl | _ | refl
      = sub (λ fs' → just (Formula.symbol s p (f ∷ fs')))
        (Vec.snoc-init-last fs)

    formula-state-to-from-formula
      (Formula.symbol s@(symbol both _ _ _ _) p (f ∷ fs)) | yes _ | yes _
      with formula-state-to-formula (formula-state-from-formula f)
      | formula-state-to-from-formula f
      | formula-state-to-formula (formula-state-from-formulas-last fs)
      | formula-state-to-from-formulas-last fs
      | sandbox-state-to-formulas (sandbox-state-from-formulas-init fs)
      | sandbox-state-to-from-formulas-init fs
    ... | _ | refl | _ | refl | _ | refl
      = sub (λ fs' → just (Formula.symbol s p (f ∷ fs')))
        (Vec.snoc-init-last fs)

    formula-state-to-from-formulas-last (f ∷ [])
      = formula-state-to-from-formula f
    formula-state-to-from-formulas-last (_ ∷ fs@(_ ∷ _))
      = formula-state-to-from-formulas-last fs

    sandbox-state-to-from-formula
      = formula-state-to-from-formula

    sandbox-state-to-from-formulas []
      = refl
    sandbox-state-to-from-formulas (f ∷ fs)
      with formula-state-to-formula (formula-state-from-formula f)
      | formula-state-to-from-formula f
      | sandbox-state-to-formulas (sandbox-state-from-formulas fs)
      | sandbox-state-to-from-formulas fs
    ... | _ | refl | _ | refl
      = refl

    sandbox-state-to-from-formulas-init (_ ∷ [])
      = refl
    sandbox-state-to-from-formulas-init (f ∷ fs@(_ ∷ _))
      with formula-state-to-formula (formula-state-from-formula f)
      | formula-state-to-from-formula f
      | sandbox-state-to-formulas (sandbox-state-from-formulas-init fs)
      | sandbox-state-to-from-formulas-init fs
    ... | _ | refl | _ | refl
      = refl

  -- #### Split

  sandbox-state-simple-split-functor
    : (ss : Symbols)
    → (vs : Variables)
    → (m : Bool)
    → SimpleSplitFunctor
      (Any (SandboxState ss vs m))
      (Formula ss vs m)
  sandbox-state-simple-split-functor _ _ _
    = record
    { base
      = record
      { base
        = sandbox-state-to-formula
      ; unbase
        = sandbox-state-from-formula
      ; base-unbase
        = sandbox-state-to-from-formula
      }
    }

  -- ### Properties
  
  module _
    {ss : Symbols}
    {vs : Variables}
    {m : Bool}
    where
  
    formula-state-left-closed-equal
      : (s : Symbol)
      → .(p : sym s ∈ ss)
      → (l : Left ss vs m s)
      → (r r' : Right ss vs m s)
      → (cs cs' : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s))
      → FormulaStateLeftClosed (symbol s p l r cs)
      → FormulaStateLeftClosed (symbol s p l r' cs')
    formula-state-left-closed-equal _ _ (nothing _) _ _ _ _
      = id
    formula-state-left-closed-equal _ _ (just _ _) _ _ _ _
      = id
  
    formula-state-right-closed-equal
      : (s : Symbol)
      → .(p : sym s ∈ ss)
      → (l l' : Left ss vs m s)
      → (r : Right ss vs m s)
      → (cs cs' : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s))
      → FormulaStateRightClosed (symbol s p l r cs)
      → FormulaStateRightClosed (symbol s p l' r cs')
    formula-state-right-closed-equal _ _ _ _ (nothing _) _ _
      = id
    formula-state-right-closed-equal _ _ _ _ (just _ _) _ _
      = id
  
-- ## Modules

-- ### Left

Left
  : Symbols
  → Variables
  → Bool
  → Symbol
  → Set
Left
  = Internal.Left

module Left where

  open Internal.Left public

  open Internal public
    using () renaming
    ( left-hole
      to hole
    )

-- ### Right

Right
  : Symbols
  → Variables
  → Bool
  → Symbol
  → Set
Right
  = Internal.Right

module Right where

  open Internal.Right public

  open Internal public
    using () renaming
    ( right-hole
      to hole
    )

-- ### FormulaState

FormulaState
  = Internal.FormulaState

module FormulaState where

  open Internal.FormulaState public
  open Internal.FormulaStateHasLeft public
  open Internal.FormulaStateHasRight public

  open Internal public
    using () renaming
    ( FormulaStateHasLeft
      to HasLeft
    ; FormulaStateHasRight
      to HasRight
    ; FormulaStateLeftClosed
      to LeftClosed
    ; FormulaStateRightClosed
      to RightClosed
    ; formula-state-construct
      to construct
    ; formula-state-left
      to left
    ; formula-state-left-closed-equal
      to left-closed-equal
    ; formula-state-right
      to right
    ; formula-state-right-closed-equal
      to right-closed-equal
    )

-- ### FormulaStatePath

FormulaStatePath
  = Internal.FormulaStatePath

open Internal.FormulaStatePath public

module FormulaStatePath where

  open Internal public
    using () renaming
    ( FormulaStatePathNotLeft
      to NotLeft
    ; FormulaStatePathNotRight
      to NotRight
    ; formula-state-path-leftmost
      to leftmost
    ; formula-state-path-rightmost
      to rightmost
    )

-- ### SandboxState

SandboxState
  = Internal.SandboxState

module SandboxState where

  open Internal.SandboxState public

  open Internal public
    using (parens-template; symbol-template; variable-template)

  open Internal public
    using () renaming
    ( SandboxStateLeftClosed
      to LeftClosed
    ; sandbox-state-hole
      to hole
    ; sandbox-state-length
      to length
    ; sandbox-state-lookup
      to lookup
    ; sandbox-state-simple-split-functor
      to simple-split-functor
    )

-- ### SandboxStatePath

SandboxStatePath
  = Internal.SandboxStatePath

open Internal.SandboxStatePath public

module SandboxStatePath where

  open Internal public
    using () renaming
    ( sandbox-state-path-cons
      to cons
    ; sandbox-state-path-left
      to left
    ; sandbox-state-path-left-leftmost
      to left-leftmost
    ; sandbox-state-path-leftmost
      to leftmost
    ; sandbox-state-path-right
      to right
    ; sandbox-state-path-right-def
      to right-def
    )
  
