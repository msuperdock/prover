module Prover.Data.Proof where

open import Prover.Data.Formula
  using (Formula; frm_∈?_)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Metas
  using (Metas)
open import Prover.Data.Rule
  using (Rule; rule) 
open import Prover.Data.Rules
  using (Rules; rul_∈_)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Variables
  using (Variables)
open import Prover.Prelude

open Vec public
  using ([]; _∷_; _!_)

-- ## Internal

module Internal where

  -- ### Definitions
  
  -- #### Branch

  data Branch
    {ss : Symbols}
    (rs : Rules ss)
    (vs : Variables)
    : Set

  branch-conclusion
    : {ss : Symbols}
    → {rs : Rules ss}
    → {vs : Variables}
    → Branch rs vs
    → Formula ss vs true

  data Branch {ss} rs vs where

    assumption
      : Formula ss vs true
      → Branch rs vs

    rule
      : (r : Rule ss)
      → .(rul r ∈ rs)
      → (bs : Vec (Branch rs vs) (Rule.arity r))
      → (c : Formula ss vs true)
      → .(Rule.Match r (Vec.map branch-conclusion bs) c)
      → Branch rs vs

  branch-conclusion (assumption c)
    = c
  branch-conclusion (rule _ _ _ c _)
    = c

  branch-arity
    : {ss : Symbols}
    → {rs : Rules ss}
    → {vs : Variables}
    → Branch rs vs
    → ℕ
  branch-arity (assumption _)
    = zero
  branch-arity (rule r _ _ _ _)
    = Rule.arity r
  
  branch-branches
    : {ss : Symbols}
    → {rs : Rules ss}
    → {vs : Variables}
    → (b : Branch rs vs)
    → Vec (Branch rs vs) (branch-arity b)
  branch-branches (assumption _)
    = []
  branch-branches (rule _ _ bs _ _)
    = bs

  -- #### BranchWith

  record BranchWith
    {ss : Symbols}
    {vs : Variables}
    (rs : Rules ss)
    (c : Formula ss vs true)
    : Set
    where

    constructor
      
      branch-with

    field

      branch
        : Branch rs vs
  
      valid
        : branch-conclusion branch ≡ c

  -- #### Proof

  record Proof
    {ss : Symbols}
    (rs : Rules ss)
    (r : Rule ss)
    : Set
    where

    constructor
    
      proof

    field
    
      branch
        : Branch rs (Rule.variables r)
  
      .valid
        : branch-conclusion branch ≡ Formula.to-meta-formula (Rule.conclusion r)

  -- #### BranchPath

  data BranchPath
    {ss : Symbols}
    {rs : Rules ss}
    {vs : Variables}
    (b : Branch rs vs)
    : Set
    where

    stop
      : BranchPath b

    go
      : (k : Fin (branch-arity b))
      → BranchPath (branch-branches b ! k)
      → BranchPath b

  -- #### BranchWithPath

  BranchWithPath
    : {ss : Symbols}
    → {vs : Variables}
    → {rs : Rules ss}
    → {c : Formula ss vs true}
    → BranchWith rs c
    → Set
  BranchWithPath (branch-with b _)
    = BranchPath b

  -- #### ProofPath

  ProofPath
    : {ss : Symbols}
    → {rs : Rules ss}
    → {r : Rule ss}
    → Proof rs r
    → Set
  ProofPath (proof b _)
    = BranchPath b

  -- ### Interface

  -- #### Branch

  module _
    {ss : Symbols}
    {rs : Rules ss}
    {vs : Variables}
    where

    branch-metas-with
      : Branch rs vs
      → Metas
      → Metas
    
    branch-metas-with'
      : {n : ℕ}
      → Vec (Branch rs vs) n
      → Metas
      → Metas
    
    branch-metas-with (assumption c)
      = Formula.metas-with c
    branch-metas-with (rule _ _ bs c _)
      = branch-metas-with' bs ∘ Formula.metas-with c
    
    branch-metas-with' []
      = id
    branch-metas-with' (b ∷ bs)
      = branch-metas-with' bs ∘ branch-metas-with b
    
    branch-metas
      : Branch rs vs
      → Metas
    branch-metas b
      = branch-metas-with b Metas.empty

    branch-lookup
      : (b : Branch rs vs)
      → BranchPath b
      → Formula ss vs true
    branch-lookup b stop
      = branch-conclusion b
    branch-lookup b (go k bp)
      = branch-lookup (branch-branches b ! k) bp

    branch-update
      : (b : Branch rs vs)
      → (bp : BranchPath b)
      → BranchWith rs (branch-lookup b bp)
      → Σ (BranchWith rs (branch-conclusion b)) BranchWithPath
    branch-update _ stop p'
      = (p' , stop)
    branch-update (rule r p bs c m) (go k bp) p'
      with branch-update (bs ! k) bp p'
    ... | (branch-with b q , pp)
      = branch-with (rule r p (Vec.update bs k b) c
        (rewrite' (λ x → Rule.Match r x c)
          (Vec.map-update branch-conclusion bs k b q) m)) refl
      , go k
        (rewrite' BranchPath
          (Vec.lookup-update bs k b) pp)
       
  -- #### Proof

  module _
    {ss : Symbols}
    {rs : Rules ss}
    {r : Rule ss}
    where

    proof-metas
      : Proof rs r
      → Metas
    proof-metas (proof b _)
      = branch-metas b

    proof-lookup
      : (p : Proof rs r)
      → ProofPath p
      → Formula ss (Rule.variables r) true
    proof-lookup (proof b _)
      = branch-lookup b

    proof-update
      : (p : Proof rs r)
      → (pp : ProofPath p)
      → BranchWith rs (proof-lookup p pp)
      → Σ (Proof rs r) ProofPath
    proof-update (proof b q) pp p
      with branch-update b pp p
    ... | (branch-with b' q' , pp')
      = (proof b' (trans q' q) , pp')

  -- #### BranchPath

  module _
    {ss : Symbols}
    {rs : Rules ss}
    {vs : Variables}
    where

    branch-path-top
      : {b : Branch rs vs}
      → BranchPath b
    branch-path-top {b = assumption _}
      = stop
    branch-path-top {b = rule _ _ [] _ _}
      = stop
    branch-path-top {b = rule _ _ (b ∷ _) _ _}
      = go zero (branch-path-top {b = b})
  
    branch-path-up
      : {b : Branch rs vs}
      → BranchPath b
      → Maybe (BranchPath b)
    branch-path-up {b = assumption _} stop
      = nothing
    branch-path-up {b = rule _ _ [] _ _} stop
      = nothing
    branch-path-up {b = rule _ _ (_ ∷ bs) _ _} stop
      = just (go (Fin.maximum (Vec.length bs)) stop)
    branch-path-up (go k bp)
      with branch-path-up bp
      | Fin.decrement k
    ... | nothing | nothing
      = nothing
    ... | nothing | just k'
      = just (go k' stop)
    ... | just bp' | _
      = just (go k bp')
  
    branch-path-down
      : {b : Branch rs vs}
      → BranchPath b
      → Maybe (BranchPath b)
    branch-path-down stop
      = nothing
    branch-path-down (go k bp)
      with branch-path-down bp
      | Fin.increment k
    ... | nothing | nothing
      = just stop
    ... | nothing | just k'
      = just (go k' branch-path-top)
    ... | just bp' | _
      = just (go k bp')
  
    branch-path-up-top
      : {b : Branch rs vs}
      → branch-path-up (branch-path-top {b = b}) ≡ nothing
    branch-path-up-top {b = assumption _}
      = refl
    branch-path-up-top {b = rule _ _ [] _ _}
      = refl
    branch-path-up-top {b = rule _ _ (b ∷ _) _ _}
      with branch-path-up (branch-path-top {b = b})
      | branch-path-up-top {b = b}
    ... | _ | refl
      = refl

  -- #### ProofPath

  module _
    {ss : Symbols}
    {rs : Rules ss}
    {r : Rule ss}
    where

    proof-path-top
      : (p : Proof rs r)
      → ProofPath p
    proof-path-top _
      = branch-path-top
  
    proof-path-up
      : (p : Proof rs r)
      → ProofPath p
      → Maybe (ProofPath p)
    proof-path-up _
      = branch-path-up
  
    proof-path-down
      : (p : Proof rs r)
      → ProofPath p
      → Maybe (ProofPath p)
    proof-path-down _
      = branch-path-down
  
    proof-path-up-top
      : (p : Proof rs r)
      → proof-path-up p (proof-path-top p) ≡ nothing
    proof-path-up-top _
      = branch-path-up-top

  -- ### Construction

  module _
    {ss : Symbols}
    {rs : Rules ss}
    {r : Rule ss}
    where

    proof-assumption
      : Proof rs r
    proof-assumption
      = record
      { branch
        = assumption (Formula.to-meta-formula (Rule.conclusion r))
      ; valid
        = refl
      }

  -- ### Completeness

  module _
    {ss : Symbols}
    where

    branch-is-complete-assumption
      : {vs : Variables}
      → List (Formula ss vs false)
      → Formula ss vs true
      → Bool
    branch-is-complete-assumption hs f
      with Formula.is-complete? f
    ... | no _
      = false
    ... | yes p
      = Bool.from-dec (frm (Formula.from-meta-formula f p) ∈? hs)

    branch-is-complete
      : {rs : Rules ss}
      → {vs : Variables}
      → List (Formula ss vs false)
      → Branch rs vs
      → Bool
    
    branch-are-complete
      : {rs : Rules ss}
      → {vs : Variables}
      → {n : ℕ}
      → List (Formula ss vs false)
      → Vec (Branch rs vs) n
      → Bool

    branch-is-complete hs (assumption f)
      = branch-is-complete-assumption hs f
    branch-is-complete hs (rule _ _ bs c _)
      = Formula.is-complete c ∧ branch-are-complete hs bs

    branch-are-complete _ []
      = true
    branch-are-complete hs (b ∷ bs)
      = branch-is-complete hs b ∧ branch-are-complete hs bs
  
    proof-is-complete
      : {rs : Rules ss}
      → {r : Rule ss}
      → Proof rs r
      → Bool
    proof-is-complete {r = r} (proof b _)
      = branch-is-complete (Rule.hypotheses r) b

  -- ### Properties

  module _
    {ss : Symbols}
    {vs : Variables}
    where

    branch-conclusions-assumptions
      : {n : ℕ}
      → (fs : Vec (Formula ss vs true) n)
      → (rs : Rules ss)
      → Vec.map branch-conclusion (Vec.map (assumption {rs = rs}) fs) ≡ fs
    branch-conclusions-assumptions [] _
      = refl
    branch-conclusions-assumptions (_ ∷ fs) rs
      = Vec.cons-equal refl (branch-conclusions-assumptions fs rs)

  -- ### Meta-substitution

  module _
    {ss : Symbols}
    {rs : Rules ss}
    where

    branch-substitute-meta
      : {vs : Variables}
      → Branch rs vs
      → Meta
      → Formula ss vs false
      → Branch rs vs
    
    branch-substitutes-meta
      : {n : ℕ}
      → {vs : Variables}
      → Vec (Branch rs vs) n
      → Meta
      → Formula ss vs false
      → Vec (Branch rs vs) n
    
    branch-conclusions-substitutes
      : {n : ℕ}
      → {vs : Variables}
      → (bs : Vec (Branch rs vs) n)
      → (m : Meta)
      → (f : Formula ss vs false)
      → Vec.map branch-conclusion (branch-substitutes-meta bs m f)
        ≡ Formula.substitutes-meta (Vec.map branch-conclusion bs) m f 
    
    branch-substitute-meta (assumption c) m f 
      = assumption (Formula.substitute-meta c m f)
    
    branch-substitute-meta (rule r q bs c rm) m f
      = rule r q
        (branch-substitutes-meta bs m f)
        (Formula.substitute-meta c m f)
        (rewrite' (λ x → Rule.Match r x (Formula.substitute-meta c m f))
          (branch-conclusions-substitutes bs m f)
          (Rule.substitute-meta-match rm))
    
    branch-substitutes-meta [] _ _
      = []
    branch-substitutes-meta (b ∷ bs) m f
      = branch-substitute-meta b m f
      ∷ branch-substitutes-meta bs m f
    
    branch-conclusions-substitutes [] _ _
      = refl
    branch-conclusions-substitutes (assumption _ ∷ bs) m f
      = Vec.cons-equal refl (branch-conclusions-substitutes bs m f)
    branch-conclusions-substitutes (rule _ _ _ _ _ ∷ bs) m f
      = Vec.cons-equal refl (branch-conclusions-substitutes bs m f)
    
    branch-conclusion-substitute
      : {vs : Variables}
      → (b : Branch rs vs)
      → (m : Meta)
      → (f : Formula ss vs false)
      → branch-conclusion (branch-substitute-meta b m f)
        ≡ Formula.substitute-meta (branch-conclusion b) m f
    branch-conclusion-substitute (assumption _) _ _
      = refl
    branch-conclusion-substitute (rule _ _ _ _ _) _ _
      = refl

    branch-substitute-meta-path
      : {vs : Variables}
      → {b : Branch rs vs}
      → BranchPath b
      → (m : Meta)
      → (f : Formula ss vs false)
      → BranchPath (branch-substitute-meta b m f)
    
    branch-substitutes-meta-path
      : {n : ℕ}
      → {vs : Variables}
      → (bs : Vec (Branch rs vs) n)
      → (k : Fin n)
      → BranchPath (bs ! k)
      → (m : Meta)
      → (f : Formula ss vs false)
      → BranchPath (branch-substitutes-meta bs m f ! k)
    
    branch-substitute-meta-path stop _ _
      = stop
    branch-substitute-meta-path {b = rule _ _ bs _ _} (go k bp) m f
      = go k (branch-substitutes-meta-path bs k bp m f)
    
    branch-substitutes-meta-path (_ ∷ _) zero bp m f
      = branch-substitute-meta-path bp m f
    branch-substitutes-meta-path (_ ∷ bs) (suc k) bp m f
      = branch-substitutes-meta-path bs k bp m f

    proof-substitute-meta 
      : {r : Rule ss}
      → (p : Proof rs r)
      → ProofPath p
      → Meta
      → Formula ss (Rule.variables r) false
      → Σ (Proof rs r) ProofPath
    proof-substitute-meta {r = rule _ _ _ c} (proof b q) pp m f
      = proof
        (branch-substitute-meta b m f)
        (trans (branch-conclusion-substitute b m f) (rewrite'
          (λ x → Formula.substitute-meta x m f ≡ Formula.to-meta-formula c) q
          (Formula.substitute-meta-to-meta-formula c m f)))
      , branch-substitute-meta-path pp m f

  -- ### Inference

  module _
    {ss : Symbols}
    {rs : Rules ss}
    where

    branch-with-infer-formula
      : {vs : Variables}
      → Metas
      → (f : Formula ss vs true)
      → (r : Rule ss)
      → rul r ∈ rs
      → Formula.Match (Rule.conclusion r) f
      → BranchWith rs f
    branch-with-infer-formula ms f r@(rule _ _ (any hs) c) p
      (Formula.match subs q)
      with Formula.substitutes-def hs subs ms
    ... | Formula.substitutes-def-result {fs' = hs'} subs' _ p' q'
      = record
      { branch
        = rule r p
          (Vec.map assumption hs') f
          (Rule.match subs'
            (rewrite' (λ x → Formula.substitutes hs subs' ≡ just x)
              (branch-conclusions-assumptions hs' rs) q')
            (Formula.⊆-substitute c subs subs' p' q))
      ; valid
        = refl
      }
  
    proof-infer
      : {r : Rule ss}
      → (p : Proof rs r)
      → (pp : ProofPath p)
      → (r' : Rule ss)
      → rul r' ∈ rs
      → Formula.Match (Rule.conclusion r') (proof-lookup p pp)
      → Σ (Proof rs r) ProofPath
    proof-infer p pp r q m
      = proof-update p pp 
        (branch-with-infer-formula (proof-metas p) (proof-lookup p pp) r q m)

-- ## Modules

-- ### Branch

Branch
  : {ss : Symbols}
  → Rules ss
  → Variables
  → Set
Branch
  = Internal.Branch

module Branch where

  open Internal.Branch public

  open Internal public using () renaming
    ( branch-conclusion
      to conclusion
    ; branch-is-complete-assumption
      to is-complete-assumption
    )

-- ### Proof

Proof
  : {ss : Symbols}
  → Rules ss
  → Rule ss
  → Set
Proof
  = Internal.Proof

open Internal public
  using (proof)

module Proof where

  open Internal public using () renaming
    ( proof-assumption
      to assumption
    ; proof-infer
      to infer
    ; proof-is-complete
      to is-complete
    ; proof-lookup
      to lookup
    ; proof-substitute-meta
      to substitute-meta
    )

-- ### BranchPath

BranchPath
  : {ss : Symbols}
  → {rs : Rules ss}
  → {vs : Variables}
  → Branch rs vs
  → Set
BranchPath
  = Internal.BranchPath

open Internal.BranchPath public

-- ### ProofPath

ProofPath
  : {ss : Symbols}
  → {rs : Rules ss}
  → {r : Rule ss}
  → Proof rs r
  → Set
ProofPath
  = Internal.ProofPath

module ProofPath where

  open Internal public using () renaming
    ( proof-path-down
      to down
    ; proof-path-top
      to top
    ; proof-path-up
      to up
    ; proof-path-up-top
      to up-top
    )

