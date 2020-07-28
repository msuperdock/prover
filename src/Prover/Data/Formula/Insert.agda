module Prover.Data.Formula.Insert where

open import Prover.Data.Formula.Construct
  using (Construct; LeftSubconstruct; RightSubconstruct)
open import Prover.Data.Formula.State
  using (FormulaState; FormulaStatePath; Left; Right; SandboxState;
    SandboxStatePath; center; end; go; left; nothing; right; stop; tt)
open import Prover.Data.Symbol
  using (Symbol; tt)
open import Prover.Data.Symbols
  using (Symbols; sym_∈_)
open import Prover.Data.Variable
  using (Variable)
open import Prover.Data.Variables
  using (Variables; var_∈_)
open import Prover.Prelude

open Vec
  using (_!_)

-- #### Split

module _
  {ss : Symbols}
  {vs : Variables}
  {m : Bool}
  where

  data LeftSubformula
    (f : FormulaState ss vs m)
    : Set
    where

    left-subformula
      : (f' : FormulaState ss vs m)
      → (FormulaState.LeftClosed f → FormulaState.LeftClosed f')
      → LeftSubconstruct
        (FormulaState.construct f)
        (FormulaState.construct f')
      → LeftSubformula f

  data RightSubformula
    (f : FormulaState ss vs m)
    : Set
    where

    right-subformula
      : (f' : FormulaState ss vs m)
      → (FormulaState.RightClosed f → FormulaState.RightClosed f')
      → RightSubconstruct
        (FormulaState.construct f)
        (FormulaState.construct f')
      → RightSubformula f

  data FormulaStateModified
    (f : FormulaState ss vs m)
    : Set
    where

    formula-state-modified
      : (f' : FormulaState ss vs m)
      → FormulaState.construct f' ≡ FormulaState.construct f
      → (FormulaState.LeftClosed f → FormulaState.LeftClosed f')
      → (FormulaState.RightClosed f → FormulaState.RightClosed f')
      → FormulaStatePath f'
      → FormulaStateModified f

  data SandboxStateModified
    (s : Any (SandboxState ss vs m))
    : Set
    where

    sandbox-state-modified
      : (s' : Any (SandboxState ss vs m))
      → (SandboxState.LeftClosed s → SandboxState.LeftClosed s')
      → SandboxStatePath s'
      → SandboxStateModified s

  data FormulaStateSplit
    (f : FormulaState ss vs m)
    : Set
    where

    simple
      : Maybe (LeftSubformula f)
      → RightSubformula f
      → FormulaStateSplit f

    complex
      : Maybe (Any (SandboxState ss vs m))
      → Maybe (Any (SandboxState ss vs m))
      → (Σ (Any (SandboxState ss vs m)) SandboxStatePath
        → FormulaStateModified f)
      → FormulaStateSplit f

  data SandboxStateSplit
    (s : Any (SandboxState ss vs m))
    : Set
    where

    simple
      : Maybe (l ∈ Any (SandboxState ss vs m)
        × (SandboxState.LeftClosed s → SandboxState.LeftClosed l))
      → Maybe (Any (SandboxState ss vs m))
      → SandboxStateSplit s

    complex
      : Maybe (Any (SandboxState ss vs m))
      → Maybe (Any (SandboxState ss vs m))
      → (Σ (Any (SandboxState ss vs m)) SandboxStatePath
        → SandboxStateModified s)
      → SandboxStateSplit s

  formula-state-split
    : (f : FormulaState ss vs m)
    → FormulaStatePath f
    → FormulaStateSplit f

  sandbox-state-split  
    : (s : Any (SandboxState ss vs m))
    → SandboxStatePath s
    → SandboxStateSplit s

  formula-state-split f@FormulaState.hole stop
    = simple nothing (right-subformula f id RightSubconstruct.reflexive)
  formula-state-split f@(FormulaState.parens _) stop
    = simple nothing (right-subformula f id RightSubconstruct.reflexive)
  formula-state-split f@(FormulaState.meta _) stop
    = simple nothing (right-subformula f id RightSubconstruct.reflexive)
  formula-state-split f@(FormulaState.variable' _ _) stop
    = simple nothing (right-subformula f id RightSubconstruct.reflexive)

  formula-state-split f@(FormulaState.symbol _ _ (nothing _) _ _) stop
    = simple nothing (right-subformula f id RightSubconstruct.reflexive)
  formula-state-split (FormulaState.symbol s p (left f lv) r cs) stop
    = simple
      (just (left-subformula f id
        (LeftSubconstruct.recursive lv LeftSubconstruct.reflexive)))
      (right-subformula (FormulaState.symbol s p Left.hole r cs)
        (FormulaState.right-closed-equal s p (left f lv) Left.hole r cs cs)
        RightSubconstruct.reflexive)

  formula-state-split (FormulaState.symbol s p l@(left f lv) r cs) (left fp)
    with formula-state-split f fp

  ... | simple nothing (right-subformula r' _ rs)
    = simple nothing
      (right-subformula
        (FormulaState.symbol s p
          (left r' (RightSubconstruct.left-valid rs s lv)) r cs)
        (FormulaState.right-closed-equal s p l
          (left r' (RightSubconstruct.left-valid rs s lv)) r cs cs)
        RightSubconstruct.reflexive)

  ... | simple (just (left-subformula l' lc ls)) (right-subformula r' _ rs)
    = simple
      (just (left-subformula l' lc
        (LeftSubconstruct.recursive lv ls)))
      (right-subformula
        (FormulaState.symbol s p
          (left r' (RightSubconstruct.left-valid rs s lv)) r cs)
        (FormulaState.right-closed-equal s p l
          (left r' (RightSubconstruct.left-valid rs s lv)) r cs cs)
        RightSubconstruct.reflexive)

  ... | complex l' r' g
    = complex l' r' ((λ {(formula-state-modified f' q lc _ fp')
      → formula-state-modified
        (FormulaState.symbol s p
          (left f' (rewrite' (Construct.LeftValid s) q lv)) r cs) refl lc
        (FormulaState.right-closed-equal s p l
          (left f' (rewrite' (Construct.LeftValid s) q lv)) r cs cs)
        (left fp')}) ∘ g)

  formula-state-split (FormulaState.symbol s p l r@(right f rv) cs) (right fp)
    with formula-state-split f fp
  ... | simple nothing (right-subformula r' rc rs)
    = simple
      (just (left-subformula
        (FormulaState.symbol s p l Right.hole cs)
        (FormulaState.left-closed-equal s p l r Right.hole cs cs)
        LeftSubconstruct.reflexive))
      (right-subformula r' rc (RightSubconstruct.recursive rv rs))

  ... | simple (just (left-subformula l' _ ls)) (right-subformula r' rc rs)
    = simple
      (just (left-subformula
        (FormulaState.symbol s p l
          (right l' (LeftSubconstruct.right-valid ls s rv)) cs)
        (FormulaState.left-closed-equal s p l r
          (right l' (LeftSubconstruct.right-valid ls s rv)) cs cs)
        LeftSubconstruct.reflexive))
      (right-subformula r' rc (RightSubconstruct.recursive rv rs))

  ... | complex l' r' g
    = complex l' r' ((λ {(formula-state-modified f' q _ rc fp')
      → formula-state-modified
        (FormulaState.symbol s p l
          (right f' (rewrite' (Construct.RightValid s) q rv)) cs) refl
        (FormulaState.left-closed-equal s p l r
          (right f' (rewrite' (Construct.RightValid s) q rv)) cs cs) rc
        (right fp')}) ∘ g)

  formula-state-split (FormulaState.parens s) (center zero sp)
    with sandbox-state-split s sp
  ... | simple l' r'
    = complex (Maybe.map π₁ l') r' (λ {(s' , sp')
      → formula-state-modified
        (FormulaState.parens s') refl id id
        (center zero sp')})
  ... | complex l' r' g
    = complex l' r' ((λ {(sandbox-state-modified s' _ sp')
      → formula-state-modified
        (FormulaState.parens s') refl id id
        (center zero sp')}) ∘ g)

  formula-state-split (FormulaState.symbol s p l r cs) (center k sp)
    with sandbox-state-split (cs ! k) sp
  ... | simple l' r'
    = complex (Maybe.map π₁ l') r' (λ {(s' , sp')
      → formula-state-modified
        (FormulaState.symbol s p l r (Vec.update cs k s')) refl
        (FormulaState.left-closed-equal s p l r r cs (Vec.update cs k s'))
        (FormulaState.right-closed-equal s p l l r cs (Vec.update cs k s'))
        (center k (rewrite' SandboxStatePath
          (Vec.lookup-update cs k s') sp'))})
  ... | complex l' r' g
    = complex l' r' ((λ {(sandbox-state-modified s' _ sp')
      → formula-state-modified
        (FormulaState.symbol s p l r (Vec.update cs k s')) refl
        (FormulaState.left-closed-equal s p l r r cs (Vec.update cs k s'))
        (FormulaState.right-closed-equal s p l l r cs (Vec.update cs k s'))
        (center k (rewrite' SandboxStatePath
          (Vec.lookup-update cs k s') sp'))}) ∘ g)

  sandbox-state-split s end
    = simple (just (s , id)) nothing

  sandbox-state-split (any (SandboxState.singleton f)) (go zero fp)
    with formula-state-split f fp
  ... | simple nothing (right-subformula r _ _)
    = simple nothing
      (just (any (SandboxState.singleton r)))
  ... | simple (just (left-subformula l lc _)) (right-subformula r _ _)
    = simple
      (just (any (SandboxState.singleton l) , lc))
      (just (any (SandboxState.singleton r)))
  ... | complex l r g
    = complex l r ((λ {(formula-state-modified f' _ lc _ fp)
      → sandbox-state-modified
        (any (SandboxState.singleton f')) lc
        (go zero fp)}) ∘ g)

  sandbox-state-split (any (SandboxState.cons f rc s lc)) (go zero fp)
    with formula-state-split f fp
  ... | simple nothing (right-subformula r rc' _)
    = simple nothing
      (just (any (SandboxState.cons r (rc' rc) s lc)))
  ... | simple (just (left-subformula l lc' _)) (right-subformula r rc' _)
    = simple
      (just (any (SandboxState.singleton l) , lc'))
      (just (any (SandboxState.cons r (rc' rc) s lc)))
  ... | complex l r g
    = complex l r ((λ {(formula-state-modified f' _ lc' rc' fp)
      → sandbox-state-modified
        (any (SandboxState.cons f' (rc' rc) s lc)) lc'
        (go zero fp)}) ∘ g)

  sandbox-state-split (any (SandboxState.cons f rc s lc)) (go (suc k) fp)
    with sandbox-state-split s (go k fp)
  ... | simple nothing r
    = simple
      (just (any (SandboxState.singleton f) , id)) r
  ... | simple (just (s' , lc')) r
    = simple
      (just (any (SandboxState.cons f rc s' (lc' lc)) , id)) r
  ... | complex l r g
    = complex l r ((λ {(sandbox-state-modified s' lc' sp)
      → sandbox-state-modified
        (any (SandboxState.cons f rc s' (lc' lc))) id
        (SandboxStatePath.cons sp)}) ∘ g)

  sandbox-state-split-tuple
    : (s : Any (SandboxState ss vs m))
    → SandboxStatePath s
    → (Maybe (Any (SandboxState ss vs m))
      × Maybe (Any (SandboxState ss vs m))
      × (Σ (Any (SandboxState ss vs m)) SandboxStatePath
        → Σ (Any (SandboxState ss vs m)) SandboxStatePath))
  sandbox-state-split-tuple s sp
    with sandbox-state-split s sp
  ... | simple l r
    = (Maybe.map π₁ l , r , id)
  ... | complex l r g
    = (l , r , (λ {(sandbox-state-modified s _ sp) → (s , sp)}) ∘ g)

-- #### Update

module _
  {ss : Symbols}
  {vs : Variables}
  {m : Bool}
  where

  formula-state-path-map-left
    : {a : ℕ}
    → {s : Symbol a}
    → .{p : sym s ∈ ss}
    → {f f' : FormulaState ss vs m}
    → {lv : Construct.LeftValid s (FormulaState.construct f)}
    → {lv' : Construct.LeftValid s (FormulaState.construct f')}
    → {r : Right ss vs m s}
    → {cs : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s)}
    → (FormulaStatePath f → FormulaStatePath f')
    → FormulaStatePath (FormulaState.symbol s p (left f lv) r cs)
    → FormulaStatePath (FormulaState.symbol s p (left f' lv') r cs)
  formula-state-path-map-left _ stop
    = stop
  formula-state-path-map-left g (left fp)
    = left (g fp)
  formula-state-path-map-left _ (right fp)
    = right fp
  formula-state-path-map-left _ (center k sp)
    = center k sp

  formula-state-path-map-right
    : {a : ℕ}
    → {s : Symbol a}
    → .{p : sym s ∈ ss}
    → {l : Left ss vs m s}
    → {f f' : FormulaState ss vs m}
    → {rv : Construct.RightValid s (FormulaState.construct f)}
    → {rv' : Construct.RightValid s (FormulaState.construct f')}
    → {cs : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s)}
    → (FormulaStatePath f → FormulaStatePath f')
    → FormulaStatePath (FormulaState.symbol s p l (right f rv) cs)
    → FormulaStatePath (FormulaState.symbol s p l (right f' rv') cs)
  formula-state-path-map-right _ stop
    = stop
  formula-state-path-map-right _ (left fp)
    = left fp
  formula-state-path-map-right g (right fp)
    = right (g fp)
  formula-state-path-map-right _ (center k sp)
    = center k sp

  formula-state-path-map-not-left
    : {a : ℕ}
    → {s : Symbol a}
    → .{p : sym s ∈ ss}
    → {l l' : Left ss vs m s}
    → {r : Right ss vs m s}
    → {cs : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s)}
    → (fp : FormulaStatePath (FormulaState.symbol s p l r cs))
    → FormulaStatePath.NotLeft fp
    → FormulaStatePath (FormulaState.symbol s p l' r cs)
  formula-state-path-map-not-left stop _
    = stop
  formula-state-path-map-not-left (right fp) _
    = right fp
  formula-state-path-map-not-left (center k sp) _
    = center k sp

  formula-state-path-map-not-right
    : {a : ℕ}
    → {s : Symbol a}
    → .{p : sym s ∈ ss}
    → {l : Left ss vs m s}
    → {r r' : Right ss vs m s}
    → {cs : Vec (Any (SandboxState ss vs m)) (Symbol.center-arity s)}
    → (fp : FormulaStatePath (FormulaState.symbol s p l r cs))
    → FormulaStatePath.NotRight fp
    → FormulaStatePath (FormulaState.symbol s p l r' cs)
  formula-state-path-map-not-right stop _
    = stop
  formula-state-path-map-not-right (left fp) _
    = left fp
  formula-state-path-map-not-right (center k sp) _
    = center k sp

  formula-state-path-cat-left
    : {A : Set}
    → {f : FormulaState ss vs m}
    → (hl : FormulaState.HasLeft f)
    → (FormulaStatePath (FormulaState.left f hl) → A)
    → ((fp : FormulaStatePath f) → FormulaStatePath.NotLeft fp → A)
    → FormulaStatePath f
    → A
  formula-state-path-cat-left tt g _ (left fp)
    = g fp
  formula-state-path-cat-left _ _ h fp@stop
    = h fp refl
  formula-state-path-cat-left _ _ h fp@(right _)
    = h fp refl
  formula-state-path-cat-left _ _ h fp@(center _ _)
    = h fp refl
  
  formula-state-path-cat-right
    : {A : Set}
    → {f : FormulaState ss vs m}
    → (hr : FormulaState.HasRight f)
    → (FormulaStatePath (FormulaState.right f hr) → A)
    → ((fp : FormulaStatePath f) → FormulaStatePath.NotRight fp → A)
    → FormulaStatePath f
    → A
  formula-state-path-cat-right tt g _ (right fp)
    = g fp
  formula-state-path-cat-right _ _ h fp@stop
    = h fp refl
  formula-state-path-cat-right _ _ h fp@(left _)
    = h fp refl
  formula-state-path-cat-right _ _ h fp@(center _ _)
    = h fp refl

  left-valid-sum
    : {a a' : ℕ}
    → (s : Symbol a)
    → (s' : Symbol a')
    → (f'' f''' : FormulaState ss vs m)
    → FormulaState.construct f''' ≡ FormulaState.construct f''
      ⊔ FormulaState.construct f''' ≡ Construct.symbol s
    → Construct.LeftValid s' (Construct.symbol s) 
    → Construct.LeftValid s' (FormulaState.construct f'')
    → Construct.LeftValid s' (FormulaState.construct f''')
  left-valid-sum _ _ _ f''' _ _ _
    with FormulaState.construct f'''
  left-valid-sum _ _ _ _ (ι₁ refl) _ lv | _
    = lv
  left-valid-sum _ _ _ _ (ι₂ refl) lv _ | _
    = lv

  right-valid-sum
    : {a a' : ℕ}
    → (s : Symbol a)
    → (s' : Symbol a')
    → (f'' f''' : FormulaState ss vs m)
    → FormulaState.construct f''' ≡ FormulaState.construct f''
      ⊔ FormulaState.construct f''' ≡ Construct.symbol s
    → Construct.RightValid s' (Construct.symbol s) 
    → Construct.RightValid s' (FormulaState.construct f'')
    → Construct.RightValid s' (FormulaState.construct f''')
  right-valid-sum _ _ _ f''' _ _ _
    with FormulaState.construct f'''
  right-valid-sum _ _ _ _ (ι₁ refl) _ rv | _
    = rv
  right-valid-sum _ _ _ _ (ι₂ refl) rv _ | _
    = rv
  
  record FormulaStateUpdateLeftResult
    (f : FormulaState ss vs m)
    (f' : FormulaState ss vs m)
    : Set
    where

    constructor

      formula-state-update-left-result

    field

      formula-state
        : FormulaState ss vs m

      construct-valid
        : FormulaState.construct formula-state ≡ FormulaState.construct f'
          ⊔ FormulaState.construct formula-state ≡ FormulaState.construct f

      left-closed
        : FormulaState.LeftClosed f'
        → FormulaState.LeftClosed formula-state

      right-closed
        : FormulaState.RightClosed f
        → FormulaState.RightClosed formula-state

      map-left
        : FormulaStatePath f'
        → FormulaStatePath formula-state

      map-not-left
        : (fp : FormulaStatePath f)
        → FormulaStatePath.NotLeft fp
        → FormulaStatePath formula-state

  formula-state-update-left
    : (f : FormulaState ss vs m)
    → FormulaState.HasLeft f
    → (f' : FormulaState ss vs m)
    → FormulaStateUpdateLeftResult f f'

  formula-state-update-left
    (FormulaState.symbol s p l@(left _ (Construct.left-valid tt _)) r cs) tt
    f'@FormulaState.hole
    = record
    { formula-state
      = FormulaState.symbol s p l' r cs
    ; construct-valid
      = ι₂ refl
    ; left-closed
      = id
    ; right-closed
      = FormulaState.right-closed-equal s p l l' r cs cs
    ; map-left
      = left
    ; map-not-left
      = formula-state-path-map-not-left
    }
    where
      l' = left f' (Construct.left-valid tt refl)

  formula-state-update-left
    (FormulaState.symbol s p l@(left _ (Construct.left-valid tt _)) r cs) tt
    f'@(FormulaState.parens _)
    = record
    { formula-state
      = FormulaState.symbol s p l' r cs
    ; construct-valid
      = ι₂ refl
    ; left-closed
      = id
    ; right-closed
      = FormulaState.right-closed-equal s p l l' r cs cs
    ; map-left
      = left
    ; map-not-left
      = formula-state-path-map-not-left
    }
    where
      l' = left f' (Construct.left-valid tt refl)

  formula-state-update-left
    (FormulaState.symbol s p l@(left _ (Construct.left-valid tt _)) r cs) tt
    f'@(FormulaState.meta _)
    = record
    { formula-state
      = FormulaState.symbol s p l' r cs
    ; construct-valid
      = ι₂ refl
    ; left-closed
      = id
    ; right-closed
      = FormulaState.right-closed-equal s p l l' r cs cs
    ; map-left
      = left
    ; map-not-left
      = formula-state-path-map-not-left
    }
    where
      l' = left f' (Construct.left-valid tt refl)

  formula-state-update-left
    (FormulaState.symbol s p l@(left _ (Construct.left-valid tt _)) r cs) tt
    f'@(FormulaState.variable' _ _)
    = record
    { formula-state
      = FormulaState.symbol s p l' r cs
    ; construct-valid
      = ι₂ refl
    ; left-closed
      = id
    ; right-closed
      = FormulaState.right-closed-equal s p l l' r cs cs
    ; map-left
      = left
    ; map-not-left
      = formula-state-path-map-not-left
    }
    where
      l' = left f' (Construct.left-valid tt refl)

  formula-state-update-left
    (FormulaState.symbol s p l@(left _ (Construct.left-valid tt _)) r cs) tt
    f'@(FormulaState.symbol s' _ _ _ _)
    with Construct.left-valid? s (Construct.symbol s')
    | Construct.right-valid? s' (Construct.symbol s)

  ... | no _ | no _
    = record
    { formula-state
      = FormulaState.symbol s p l' r cs
    ; construct-valid
      = ι₂ refl
    ; left-closed
      = const refl
    ; right-closed
      = FormulaState.right-closed-equal s p l l' r cs cs
    ; map-left
      = λ fp → left (center zero (go zero fp))
    ; map-not-left
      = formula-state-path-map-not-left
    }
    where
      l' = left
        (FormulaState.parens (any (SandboxState.singleton f')))
        (Construct.left-valid tt refl)
  
  ... | yes lv | _
    = record
    { formula-state
      = FormulaState.symbol s p l' r cs
    ; construct-valid
      = ι₂ refl
    ; left-closed
      = id
    ; right-closed
      = FormulaState.right-closed-equal s p l l' r cs cs
    ; map-left
      = left
    ; map-not-left
      = formula-state-path-map-not-left
    }
    where
      l' = left f' lv

  formula-state-update-left
    f@(FormulaState.symbol s _ _ _ _) hl
    (FormulaState.symbol s' p' l' r'@(right f'' rv') cs')
    | _ | yes rv@(Construct.right-valid tt _)
    with formula-state-update-left f hl f''

  ... | formula-state-update-left-result f''' q _ rc g'' g
    = record
    { formula-state
      = FormulaState.symbol s' p' l' r'' cs'
    ; construct-valid
      = ι₁ refl
    ; left-closed
      = FormulaState.left-closed-equal s' p' l' r' r'' cs' cs'
    ; right-closed
      = rc
    ; map-left
      = formula-state-path-map-right g''
    ; map-not-left
      = λ fp ¬l → right (g fp ¬l)
    }
    where
      r'' = right f''' (right-valid-sum s s' f'' f''' q rv rv')

  record FormulaStateUpdateRightResult
    (f : FormulaState ss vs m)
    (f' : FormulaState ss vs m)
    : Set
    where

    constructor

      formula-state-update-right-result

    field

      formula-state
        : FormulaState ss vs m

      construct-valid
        : FormulaState.construct formula-state ≡ FormulaState.construct f'
          ⊔ FormulaState.construct formula-state ≡ FormulaState.construct f

      right-closed
        : FormulaState.RightClosed f'
        → FormulaState.RightClosed formula-state

      left-closed
        : FormulaState.LeftClosed f
        → FormulaState.LeftClosed formula-state

      map-right
        : FormulaStatePath f'
        → FormulaStatePath formula-state

      map-not-right
        : (fp : FormulaStatePath f)
        → FormulaStatePath.NotRight fp
        → FormulaStatePath formula-state

  formula-state-update-right
    : (f : FormulaState ss vs m)
    → FormulaState.HasRight f
    → (f' : FormulaState ss vs m)
    → FormulaStateUpdateRightResult f f'

  formula-state-update-right
    (FormulaState.symbol s p l r@(right _ (Construct.right-valid tt _)) cs) tt
    f'@FormulaState.hole
    = record
    { formula-state
      = FormulaState.symbol s p l r' cs
    ; construct-valid
      = ι₂ refl
    ; right-closed
      = id
    ; left-closed
      = FormulaState.left-closed-equal s p l r r' cs cs
    ; map-right
      = right
    ; map-not-right
      = formula-state-path-map-not-right
    }
    where
      r' = right f' (Construct.right-valid tt refl)

  formula-state-update-right
    (FormulaState.symbol s p l r@(right _ (Construct.right-valid tt _)) cs) tt
    f'@(FormulaState.parens _)
    = record
    { formula-state
      = FormulaState.symbol s p l r' cs
    ; construct-valid
      = ι₂ refl
    ; right-closed
      = id
    ; left-closed
      = FormulaState.left-closed-equal s p l r r' cs cs
    ; map-right
      = right
    ; map-not-right
      = formula-state-path-map-not-right
    }
    where
      r' = right f' (Construct.right-valid tt refl)

  formula-state-update-right
    (FormulaState.symbol s p l r@(right _ (Construct.right-valid tt _)) cs) tt
    f'@(FormulaState.meta _)
    = record
    { formula-state
      = FormulaState.symbol s p l r' cs
    ; construct-valid
      = ι₂ refl
    ; right-closed
      = id
    ; left-closed
      = FormulaState.left-closed-equal s p l r r' cs cs
    ; map-right
      = right
    ; map-not-right
      = formula-state-path-map-not-right
    }
    where
      r' = right f' (Construct.right-valid tt refl)

  formula-state-update-right
    (FormulaState.symbol s p l r@(right _ (Construct.right-valid tt _)) cs) tt
    f'@(FormulaState.variable' _ _)
    = record
    { formula-state
      = FormulaState.symbol s p l r' cs
    ; construct-valid
      = ι₂ refl
    ; right-closed
      = id
    ; left-closed
      = FormulaState.left-closed-equal s p l r r' cs cs
    ; map-right
      = right
    ; map-not-right
      = formula-state-path-map-not-right
    }
    where
      r' = right f' (Construct.right-valid tt refl)

  formula-state-update-right
    (FormulaState.symbol s p l r@(right _ (Construct.right-valid tt _)) cs) tt
    f'@(FormulaState.symbol s' _ _ _ _)
    with Construct.right-valid? s (Construct.symbol s')
    | Construct.left-valid? s' (Construct.symbol s)

  ... | no _ | no _
    = record
    { formula-state
      = FormulaState.symbol s p l r' cs
    ; construct-valid
      = ι₂ refl
    ; right-closed
      = const refl
    ; left-closed
      = FormulaState.left-closed-equal s p l r r' cs cs
    ; map-right
      = λ fp → right (center zero (go zero fp))
    ; map-not-right
      = formula-state-path-map-not-right
    }
    where
      r' = right
        (FormulaState.parens (any (SandboxState.singleton f')))
        (Construct.right-valid tt refl)
  
  ... | yes rv | _
    = record
    { formula-state
      = FormulaState.symbol s p l r' cs
    ; construct-valid
      = ι₂ refl
    ; right-closed
      = id
    ; left-closed
      = FormulaState.left-closed-equal s p l r r' cs cs
    ; map-right
      = right
    ; map-not-right
      = formula-state-path-map-not-right
    }
    where
      r' = right f' rv

  formula-state-update-right
    f@(FormulaState.symbol s _ _ _ _) hr
    (FormulaState.symbol s' p' l'@(left f'' lv') r' cs')
    | _ | yes lv@(Construct.left-valid tt _)
    with formula-state-update-right f hr f''

  ... | formula-state-update-right-result f''' q _ lc g'' g
    = record
    { formula-state
      = FormulaState.symbol s' p' l'' r' cs'
    ; construct-valid
      = ι₁ refl
    ; right-closed
      = FormulaState.right-closed-equal s' p' l' l'' r' cs' cs'
    ; left-closed
      = lc
    ; map-right
      = formula-state-path-map-left g''
    ; map-not-right
      = λ fp ¬r → left (g fp ¬r)
    }
    where
      l'' = left f''' (left-valid-sum s s' f'' f''' q lv lv')

-- #### Insert

module _
  {ss : Symbols}
  {vs : Variables}
  {m : Bool}
  where

  record FormulaStateSeparated
    (f₁ f₂ : FormulaState ss vs m)
    : Set
    where
    
    constructor
      
      formula-state-separated

    field

      right-closed
        : FormulaState.RightClosed f₁

      left-closed
        : FormulaState.LeftClosed f₂

  record FormulaStateCombined
    (f₁ f₂ : FormulaState ss vs m)
    : Set
    where

    constructor
     
      formula-state-combined

    field

      formula-state
        : FormulaState ss vs m

      left-closed
        : FormulaState.LeftClosed f₁
        → FormulaState.LeftClosed formula-state

      right-closed
        : FormulaState.RightClosed f₂
        → FormulaState.RightClosed formula-state

      map-left
        : FormulaStatePath f₁
        → FormulaStatePath formula-state
      
      map-right
        : FormulaStatePath f₂
        → FormulaStatePath formula-state

  record SandboxStateCombined
    (s₁ s₂ : Any (SandboxState ss vs m))
    : Set
    where
    
    constructor

      sandbox-state-combined

    field

      sandbox-state
        : Any (SandboxState ss vs m)

      left-closed
        : SandboxState.LeftClosed s₁
        → SandboxState.LeftClosed sandbox-state

      map-left
        : SandboxStatePath s₁
        → SandboxStatePath sandbox-state

      map-right
        : SandboxStatePath s₂
        → SandboxStatePath sandbox-state

  -- Put the second FormulaState in the leftmost hole of the first, if any.
  formula-state-insert-left
    : (f : FormulaState ss vs m)
    → (f' : FormulaState ss vs m)
    → FormulaState.LeftClosed f ⊔ FormulaStateCombined f' f

  formula-state-insert-left (FormulaState.parens _) _
    = ι₁ refl
  formula-state-insert-left (FormulaState.meta _) _
    = ι₁ refl
  formula-state-insert-left (FormulaState.variable' _ _) _
    = ι₁ refl
  formula-state-insert-left (FormulaState.symbol _ _ (nothing _) _ _) _
    = ι₁ refl

  formula-state-insert-left FormulaState.hole f'
    = ι₂
    $ record
    { formula-state
      = f'
    ; left-closed
      = id
    ; right-closed
      = λ ()
    ; map-left
      = id
    ; map-right
      = const FormulaStatePath.rightmost
    }

  formula-state-insert-left f@(FormulaState.symbol _ _ (left f'' _) _ _) f'
    with formula-state-insert-left f'' f'
  ... | ι₁ lc
    = ι₁ lc
  ... | ι₂ (formula-state-combined f''' lc' _ g' g'')
    with formula-state-update-left f tt f'''
  ... | formula-state-update-left-result f'''' _ lc''' rc g''' g
    = ι₂
    $ record
    { formula-state
      = f''''
    ; left-closed
      = lc''' ∘ lc'
    ; right-closed
      = rc
    ; map-left
      = g''' ∘ g'
    ; map-right
      = formula-state-path-cat-left tt (g''' ∘ g'') g
    }

  -- Put the second FormulaState in the rightmost hole of the first, if any.
  formula-state-insert-right
    : (f : FormulaState ss vs m)
    → (f' : FormulaState ss vs m)
    → FormulaState.RightClosed f ⊔ FormulaStateCombined f f'

  formula-state-insert-right (FormulaState.parens _) _
    = ι₁ refl
  formula-state-insert-right (FormulaState.meta _) _
    = ι₁ refl
  formula-state-insert-right (FormulaState.variable' _ _) _
    = ι₁ refl
  formula-state-insert-right (FormulaState.symbol _ _ _ (nothing _) _) _
    = ι₁ refl

  formula-state-insert-right FormulaState.hole f'
    = ι₂
    $ record
    { formula-state
      = f'
    ; left-closed
      = λ ()
    ; right-closed
      = id
    ; map-left
      = const FormulaStatePath.rightmost
    ; map-right
      = id
    }

  formula-state-insert-right f@(FormulaState.symbol _ _ _ (right f'' _) _) f'
    with formula-state-insert-right f'' f'
  ... | ι₁ rc
    = ι₁ rc
  ... | ι₂ (formula-state-combined f''' _ rc' g'' g')
    with formula-state-update-right f tt f'''
  ... | formula-state-update-right-result f'''' _ rc''' lc g''' g
    = ι₂
    $ record
    { formula-state
      = f''''
    ; left-closed
      = lc
    ; right-closed
      = rc''' ∘ rc'
    ; map-left
      = formula-state-path-cat-right tt (g''' ∘ g'') g
    ; map-right
      = g''' ∘ g'
    }

  -- Indicates which formula should be considered the main formula.
  data CombinePreference
    : Set
    where

    left
      : CombinePreference

    right
      : CombinePreference

  formula-state-combine
    : CombinePreference
    → (f₁ : FormulaState ss vs m)
    → (f₂ : FormulaState ss vs m)
    → FormulaStateSeparated f₁ f₂ ⊔ FormulaStateCombined f₁ f₂
  formula-state-combine left f₁ f₂
    with formula-state-insert-right f₁ f₂
    | formula-state-insert-left f₂ f₁
  ... | ι₂ fc | _
    = ι₂ fc
  ... | _ | ι₂ fc
    = ι₂ fc
  ... | ι₁ rc | ι₁ lc
    = ι₁
    $ record
    { right-closed
      = rc
    ; left-closed
      = lc
    }

  formula-state-combine right f₁ f₂
    with formula-state-insert-left f₂ f₁
    | formula-state-insert-right f₁ f₂
  ... | ι₂ fc | _
    = ι₂ fc
  ... | _ | ι₂ fc
    = ι₂ fc
  ... | ι₁ lc | ι₁ rc
    = ι₁
    $ record
    { right-closed
      = rc
    ; left-closed
      = lc
    }

  sandbox-state-combine
    : CombinePreference
    → (s₁ : Any (SandboxState ss vs m))
    → (s₂ : Any (SandboxState ss vs m))
    → SandboxStateCombined s₁ s₂

  sandbox-state-combine cp
    (any (SandboxState.singleton f₁))
    (any (SandboxState.singleton f₂))
    with formula-state-combine cp f₁ f₂

  ... | ι₁ (formula-state-separated rc₁ lc₂)
    = record
    { sandbox-state
      = any (SandboxState.cons f₁ rc₁
        (any (SandboxState.singleton f₂)) lc₂)
    ; left-closed
      = id
    ; map-left
      = λ
      { (go zero path)
        → go zero path
      ; end
        → go (suc zero) FormulaStatePath.leftmost
      }
    ; map-right
      = SandboxStatePath.cons
    }

  ... | ι₂ (formula-state-combined f lc _ g₁ g₂)
    = record
    { sandbox-state
      = any (SandboxState.singleton f)
    ; left-closed
      = lc
    ; map-left
      = λ 
      { (go zero path)
        → go zero (g₁ path)
      ; end
        → go zero (g₂ FormulaStatePath.leftmost)
      }
    ; map-right
      = λ
      { (go zero path)
        → go zero (g₂ path)
      ; end
        → end
      }
    }

  sandbox-state-combine cp
    (any (SandboxState.singleton f₁))
    (any (SandboxState.cons f₂ rc₂ s₂ lc₂))
    with formula-state-combine cp f₁ f₂

  ... | ι₁ (formula-state-separated rc₁ lc₁)
    = record
    { sandbox-state
      = any (SandboxState.cons f₁ rc₁
        (any (SandboxState.cons f₂ rc₂ s₂ lc₂)) lc₁)
    ; left-closed
      = id
    ; map-left
      = λ
      { (go zero path)
        → go zero path
      ; end
        → go (suc zero) FormulaStatePath.leftmost
      }
    ; map-right
      = SandboxStatePath.cons
    }
  
  ... | ι₂ (formula-state-combined f lc rc g₁ g₂)
    = record
    { sandbox-state
      = any (SandboxState.cons f (rc rc₂) s₂ lc₂)
    ; left-closed
      = lc
    ; map-left
      = λ
      { (go zero path)
        → go zero (g₁ path)
      ; end
        → go zero (g₂ FormulaStatePath.leftmost)
      }
    ; map-right
      = λ
      { (go zero path)
        → go zero (g₂ path)
      ; (go (suc k) path)
        → go (suc k) path
      ; end
        → end
      }
    }

  sandbox-state-combine cp (any (SandboxState.cons f₁ rc₁ s₁ lc₁)) s₂
    with sandbox-state-combine cp s₁ s₂
  ... | sandbox-state-combined s l g₁ g₂
    = record
    { sandbox-state
      = any (SandboxState.cons f₁ rc₁ s (l lc₁))
    ; left-closed
      = id
    ; map-left
      = λ
      { (go zero path)
        → go zero path
      ; (go (suc k) path)
        → SandboxStatePath.cons (g₁ (go k path))
      ; end
        → SandboxStatePath.cons (g₁ end)
      }
    ; map-right
      = SandboxStatePath.cons ∘ g₂
    }

  -- Prepend the second SandboxState to the beginning of the first.
  sandbox-state-prepend
    : (s₁ : Any (SandboxState ss vs m))
    → SandboxStatePath s₁
    → Any (SandboxState ss vs m)
    → Σ (Any (SandboxState ss vs m)) SandboxStatePath
  sandbox-state-prepend s₁ sp s₂
    with sandbox-state-combine right s₂ s₁
  ... | sandbox-state-combined s _ _ sp'
    = (s , sp' sp)

  -- Append the second SandboxState to the end of the first.
  sandbox-state-append
    : (s₁ : Any (SandboxState ss vs m))
    → SandboxStatePath s₁
    → Any (SandboxState ss vs m)
    → Σ (Any (SandboxState ss vs m)) SandboxStatePath
  sandbox-state-append s₁ sp s₂
    with sandbox-state-combine left s₁ s₂
  ... | sandbox-state-combined s _ sp' _
    = (s , sp' sp)

  -- Insert the second SandboxState into the first.
  sandbox-state-insert
    : (s₁ : Any (SandboxState ss vs m))
    → SandboxStatePath s₁
    → (s₂ : Any (SandboxState ss vs m))
    → SandboxStatePath s₂
    → Σ (Any (SandboxState ss vs m)) SandboxStatePath
  sandbox-state-insert s₁ sp₁ s₂ sp₂
    with sandbox-state-split-tuple s₁ sp₁
  ... | (l , r , g)
    with g
    $ maybe r id (λ {s' (s , sp) → sandbox-state-append s sp s'})
    $ maybe l id (λ {s' (s , sp) → sandbox-state-prepend s sp s'})
    $ (s₂ , sp₂)
  ... | (s , sp)
    = (s , SandboxStatePath.right-def sp)

  sandbox-state-insert-parens
    : (s₁ : Any (SandboxState ss vs m))
    → SandboxStatePath s₁
    → Σ (Any (SandboxState ss vs m)) SandboxStatePath
  sandbox-state-insert-parens s₁ sp₁
    = sandbox-state-insert s₁ sp₁
      SandboxState.parens-template
      (go zero stop)

  sandbox-state-insert-variable
    : (s₁ : Any (SandboxState ss vs m))
    → SandboxStatePath s₁
    → (v : Variable)
    → .(var v ∈ vs)
    → Σ (Any (SandboxState ss vs m)) SandboxStatePath
  sandbox-state-insert-variable s₁ sp₁ v p
    = sandbox-state-insert s₁ sp₁
      (SandboxState.variable-template v p)
      (go zero stop)

  sandbox-state-insert-symbol
    : {a : ℕ}
    → (s₁ : Any (SandboxState ss vs m))
    → SandboxStatePath s₁
    → (s : Symbol a)
    → .(sym s ∈ ss)
    → Σ (Any (SandboxState ss vs m)) SandboxStatePath
  sandbox-state-insert-symbol s₁ sp₁ s p
    = sandbox-state-insert s₁ sp₁
      (SandboxState.symbol-template s p)
      (go zero stop)

