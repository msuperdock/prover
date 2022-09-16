module Prover.Draw.Formula where

open import Prover.Data.Any
  using (Any; any)
open import Prover.Data.Bool
  using (Bool)
open import Prover.Data.Fin
  using (Fin; zero; suc)
open import Prover.Data.Formula.State
  using (FormulaState; FormulaStatePath; Left; Right; SandboxState;
    SandboxStatePath; center; end; go; left; right; stop)
open import Prover.Data.Function
  using (_$_)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Nat
  using (module Nat; ℕ; suc)
open import Prover.Data.String
  using (String)
open import Prover.Data.Symbol
  using (Symbol)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Token
  using (Token)
open import Prover.Data.Variable
  using (Variable)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Data.Vec
  using (Vec; []; _∷_; _!_)
open import Prover.Draw.Meta
  using (draw-meta)
open import Prover.View.RichText
  using (RichText; RichTextPath; plain; style; text)

-- ## Types

module _
  {ss : Symbols}
  {vs : Variables}
  {m : Bool}
  where

  draw-formula
    : FormulaState ss vs m
    → RichText
  
  draw-formula-left
    : {s : Symbol}
    → Left ss vs m s
    → RichText

  draw-formula-right
    : {s : Symbol}
    → Right ss vs m s
    → RichText

  draw-formula-center
    : {n : ℕ}
    → Vec Token (suc n)
    → Vec (Any (SandboxState ss vs m)) n
    → RichText

  draw-sandbox
    : Any (SandboxState ss vs m)
    → RichText
  
  draw-formula FormulaState.hole
    = RichText.plain (String.to-list "_")
  draw-formula (FormulaState.parens s)
    = RichText.wrap "(" ")" (draw-sandbox s)
  draw-formula (FormulaState.meta m)
    = draw-meta (String.to-list (Nat.show m))
  draw-formula (FormulaState.variable' v _)
    = RichText.plain (Token.characters (Variable.token v))
  draw-formula (FormulaState.symbol s _ l r cs)
    = RichText.texts
    $ any
    $ draw-formula-left l
    ∷ draw-formula-center (Symbol.tokens s) cs
    ∷ draw-formula-right r
    ∷ []

  draw-formula-left (Left.nothing _)
    = RichText.plain (any [])
  draw-formula-left (Left.just f _)
    = draw-formula f

  draw-formula-right (Right.nothing _)
    = RichText.plain (any [])
  draw-formula-right (Right.just f _)
    = draw-formula f

  draw-formula-center (t ∷ []) []
    = RichText.plain (Token.characters t)
  draw-formula-center (t ∷ ts@(_ ∷ _)) (s ∷ ss)
    = RichText.texts
    $ any
    $ RichText.plain (Token.characters t)
    ∷ draw-sandbox s
    ∷ draw-formula-center ts ss
    ∷ []

  draw-sandbox (any (SandboxState.singleton f))
    = draw-formula f
  draw-sandbox (any (SandboxState.cons f _ s _))
    = RichText.texts
    $ any
    $ draw-formula f
    ∷ RichText.plain (String.to-list "   ")
    ∷ draw-sandbox s
    ∷ []

-- ## Paths

module _
  {ss : Symbols}
  {vs : Variables}
  {m : Bool}
  where

  draw-path-formula
    : (f : FormulaState ss vs m)
    → FormulaStatePath f
    → RichTextPath (draw-formula f)

  draw-path-formula-center-stop
    : {n : ℕ}
    → (ts : Vec Token (suc n))
    → (ss : Vec (Any (SandboxState ss vs m)) n)
    → RichTextPath (draw-formula-center ts ss)

  draw-path-formula-center
    : {n : ℕ}
    → (ts : Vec Token (suc n))
    → (ss : Vec (Any (SandboxState ss vs m)) n)
    → (k : Fin n)
    → SandboxStatePath (ss ! k)
    → RichTextPath (draw-formula-center ts ss)

  draw-path-sandbox
    : (s : Any (SandboxState ss vs m))
    → SandboxStatePath s
    → Maybe (RichTextPath (draw-sandbox s))

  draw-path-sandbox-go
    : (s : Any (SandboxState ss vs m))
    → (k : Fin (SandboxState.length s))
    → FormulaStatePath (SandboxState.lookup s k)
    → RichTextPath (draw-sandbox s)

  draw-path-formula FormulaState.hole stop
    = plain zero
  draw-path-formula (FormulaState.parens _) stop
    = text zero (plain zero)
  draw-path-formula (FormulaState.parens s) (center zero (go k fp))
    = text (suc zero) (draw-path-sandbox-go s k fp)
  draw-path-formula (FormulaState.parens _) (center zero end)
    = text (suc (suc zero)) (plain zero)
  draw-path-formula (FormulaState.meta _) stop
    = style (text zero (plain zero))
  draw-path-formula (FormulaState.variable' v _) stop
    = plain (Token.index (Variable.token v))
  draw-path-formula (FormulaState.symbol _ _ (Left.just f _) _ _) (left fp)
    = text zero (draw-path-formula f fp)
  draw-path-formula (FormulaState.symbol s _ _ _ cs) stop
    = text (suc zero) (draw-path-formula-center-stop (Symbol.tokens s) cs)
  draw-path-formula (FormulaState.symbol s _ _ _ cs) (center k sp)
    = text (suc zero) (draw-path-formula-center (Symbol.tokens s) cs k sp)
  draw-path-formula (FormulaState.symbol _ _ _ (Right.just f _) _) (right fp)
    = text (suc (suc zero)) (draw-path-formula f fp)

  draw-path-formula-center-stop (t ∷ []) []
    = plain (Token.index t)
  draw-path-formula-center-stop (t ∷ _ ∷ _) (_ ∷ _)
    = text zero (plain (Token.index t))

  draw-path-formula-center (_ ∷ _ ∷ _) (s ∷ _) zero (go k fp)
    = text (suc zero) (draw-path-sandbox-go s k fp)
  draw-path-formula-center (_ ∷ ts@(_ ∷ _)) (_ ∷ ss) zero end
    = text (suc (suc zero)) (draw-path-formula-center-stop ts ss)
  draw-path-formula-center (_ ∷ ts@(_ ∷ _)) (_ ∷ ss) (suc k) sp
    = text (suc (suc zero)) (draw-path-formula-center ts ss k sp)

  draw-path-sandbox s (go k fp)
    = just (draw-path-sandbox-go s k fp)
  draw-path-sandbox _ end
    = nothing

  draw-path-sandbox-go (any (SandboxState.singleton f)) zero fp
    = draw-path-formula f fp
  draw-path-sandbox-go (any (SandboxState.cons f _ _ _)) zero fp
    = text zero (draw-path-formula f fp)
  draw-path-sandbox-go (any (SandboxState.cons _ _ s _)) (suc k) fp
    = text (suc (suc zero)) (draw-path-sandbox-go s k fp)

