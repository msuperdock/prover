module Prover.Draw.Proof where

open import Editor.Simple
  using (SimpleSplitEditor)

open import Prover.Data.Any
  using (any)
open import Prover.Data.Bool
  using (Bool; false; true)
open import Prover.Data.Fin
  using (Fin; suc; zero)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.List
  using (List)
open import Prover.Data.Nat
  using (ℕ)
open import Prover.Data.Proof
  using (Branch; BranchPath; Proof; ProofPath; go; proof; stop)
open import Prover.Data.Rule
  using (Rule)
open import Prover.Data.Rules
  using (Rules)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Data.Vec
  using (Vec; []; _∷_; _!_)
open import Prover.Draw.Tree
  using (draw-tree; draw-tree-with)
open import Prover.Editor.Simple.Formula
  using (simple-split-editor-formula)
open import Prover.View.Line
  using (Line; line)
open import Prover.View.RichText
  using (RichText)
open import Prover.View.Tree
  using (Tree; TreePath; go; stop)

-- ## Branch

module _
  {ss : Symbols}
  {rs : Rules ss}
  {vs : Variables}
  where

  draw-status
    : List (Formula ss vs false)
    → Formula ss vs true
    → Bool
  draw-status hs f
    = Branch.is-complete-assumption hs f

  draw-formula
    : Formula ss vs true
    → RichText
  draw-formula
    = SimpleSplitEditor.draw-pure (simple-split-editor-formula ss vs true)

  draw-branch
    : List (Formula ss vs false)
    → Branch rs vs
    → Tree

  draw-branches
    : {n : ℕ}
    → List (Formula ss vs false)
    → Vec (Branch rs vs) n
    → Vec Tree n

  draw-branch hs (Branch.assumption f)
    = Tree.leaf (line (draw-status hs f) (draw-formula f))
  draw-branch _ (Branch.rule _ _ [] c _)
    = Tree.leaf (line true (draw-formula c))
  draw-branch hs (Branch.rule _ _ bs@(_ ∷ _) c _)
    = Tree.node (any (draw-branches hs bs)) (line true (draw-formula c))

  draw-branches _ []
    = []
  draw-branches hs (b ∷ bs)
    = draw-branch hs b ∷ draw-branches hs bs
  
  draw-path-branch
    : (hs : List (Formula ss vs false))
    → (b : Branch rs vs)
    → BranchPath b
    → TreePath (draw-branch hs b)

  draw-path-branches
    : {n : ℕ}
    → (hs : List (Formula ss vs false))
    → (bs : Vec (Branch rs vs) n)
    → (k : Fin n)
    → BranchPath (bs ! k)
    → TreePath (draw-branches hs bs ! k)

  draw-path-branch _ _ stop
    = stop
  draw-path-branch hs (Branch.rule _ _ bs@(_ ∷ _) _ _) (go k bp)
    = go k (draw-path-branches hs bs k bp)

  draw-path-branches hs (b ∷ _) zero bp
    = draw-path-branch hs b bp
  draw-path-branches hs (_ ∷ bs) (suc k) bp
    = draw-path-branches hs bs k bp

-- ## Proof

module _
  {ss : Symbols}
  {rs : Rules ss}
  {r : Rule ss}
  where

  draw-proof
    : Proof rs r
    → List Line
  draw-proof (proof b _)
    = draw-tree
      (draw-branch (Rule.hypotheses r) b)
  
  draw-proof-with
    : (p : Proof rs r)
    → ProofPath p
    → List Line
  draw-proof-with (proof b _) bp
    = draw-tree-with
      (draw-branch (Rule.hypotheses r) b)
      (draw-path-branch (Rule.hypotheses r) b bp)

