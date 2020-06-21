module Prover.Data.Rule where

open import Prover.Data.Identifier
  using (Identifier; _≟_idn)
open import Prover.Data.Formula
  using (Formula; Substitutions; _≟_frm; _≟_frms)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Variables
  using (Variables; _≟_vars)
open import Prover.Prelude

-- ## Definition

module _Rule where

  record Rule
    (ss : Symbols)
    (a : ℕ)
    : Set
    where

    constructor
    
      rule

    field

      name
        : Identifier

      variables
        : Variables

      hypotheses
        : Vec (Formula ss variables false) a

      conclusion
        : Formula ss variables false

Rule
  : Symbols
  → ℕ
  → Set
Rule
  = _Rule.Rule

open _Rule public
  using (rule)

-- ## Module

module Rule where

  open _Rule.Rule public

  -- ### Equality

  module _
    {ss : Symbols}
    where

    _≟_rul
      : {a : ℕ}
      → Decidable (Rule ss a)
    rule n₁ vs₁ hs₁ c₁ ≟ rule n₂ vs₂ hs₂ c₂ rul
      with n₁ ≟ n₂ idn
      | vs₁ ≟ vs₂ vars
  
    ... | no ¬p | _
      = no (λ {refl → ¬p refl})
    ... | _ | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl | yes refl
      with hs₁ ≟ hs₂ frms
      | c₁ ≟ c₂ frm
    
    ... | no ¬p | _
      = no (λ {refl → ¬p refl})
    ... | _ | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl | yes refl
      = yes refl
    
    _≟_rul?
      : Decidable (Any (Rule ss))
    _≟_rul?
      = Any.decidable (Rule ss) _≟_nat _≟_rul

  -- ### Matching

  module _
    {ss : Symbols}
    {vs : Variables}
    {a : ℕ}
    where

    record Match
      (r : Rule ss a)
      (fs : Vec (Formula ss vs true) a)
      (f : Formula ss vs true)
      : Set
      where
  
      constructor
      
        match
  
      field
  
        substitutions
          : Substitutions ss vs
  
        hypotheses-valid
          : Formula.substitutes (hypotheses r) substitutions ≡ just fs
  
        conclusion-valid
          : Formula.substitute (conclusion r) substitutions ≡ just f
  
    match?
      : (r : Rule ss a)
      → (fs : Vec (Formula ss vs true) a)
      → (f : Formula ss vs true)
      → Dec (Match r fs f)
    match? (rule _ _ hs c) fs f
      with Formula.matches-with? Map.empty (c ∷ hs) (f ∷ fs)

    ... | Formula.yes (Formula.matches-with-minimal subs _ p _)
      = yes
      $ record
      { substitutions
        = subs
      ; hypotheses-valid
        = Formula.substitutes-to-substitutes c hs subs f fs p
      ; conclusion-valid
        = Formula.substitutes-to-substitute c hs subs f fs p
      }

    ... | Formula.no p
      = no (λ {(match subs q r)
        → p (Formula.matches-with subs (Map.⊆-empty subs)
          (Formula.substitutes-recursive c hs subs f fs r q))})
  
    substitute-meta-match
      : {r : Rule ss a}
      → {fs : Vec (Formula ss vs true) a}
      → {m : Meta}
      → {f' : Formula ss vs false}
      → {f : Formula ss vs true}
      → Match r fs f
      → Match r
        (Formula.substitutes-meta fs m f')
        (Formula.substitute-meta f m f')
    substitute-meta-match
      {r = rule _ _ hs c} {fs = fs} {m = m} {f' = f'} {f = f}
      (match subs p q)
      = record
      { substitutions
        = Formula.substitute-meta-substitutions subs m f'
      ; hypotheses-valid
        = Formula.substitutes-substitute-meta-substitutions hs subs m f' fs p
      ; conclusion-valid
        = Formula.substitute-substitute-meta-substitutions c subs m f' f q
      }
  
-- ## Exports

open Rule public
  using (_≟_rul; _≟_rul?)

