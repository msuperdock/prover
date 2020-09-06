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

open Vec
  using (_∷_)

-- ## Definition

module _Rule where

  record Rule
    (ss : Symbols)
    : Set
    where

    constructor
    
      rule

    field

      {arity}
        : ℕ

      name
        : Identifier

      variables
        : Variables

      hypotheses
        : Vec (Formula ss variables false) arity

      conclusion
        : Formula ss variables false

Rule
  : Symbols
  → Set
Rule
  = _Rule.Rule

open _Rule public
  using (rule)

-- ## Module

module Rule where

  open _Rule.Rule public

  open _Rule public
    using (rule)

  -- ### Equality

  module _
    {ss : Symbols}
    where

    _≟_rul
      : Decidable (Equal (Rule ss))
    rule {a₁} n₁ vs₁ hs₁ c₁ ≟ rule {a₂} n₂ vs₂ hs₂ c₂ rul
      with a₁ ≟ a₂ nat
      | n₁ ≟ n₂ idn
      | vs₁ ≟ vs₂ vars
  
    ... | no ¬p | _ | _
      = no (λ {refl → ¬p refl})
    ... | _ | no ¬p | _
      = no (λ {refl → ¬p refl})
    ... | _ | _ | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl | yes refl | yes refl
      with hs₁ ≟ hs₂ frms
      | c₁ ≟ c₂ frm
    
    ... | no ¬p | _
      = no (λ {refl → ¬p refl})
    ... | _ | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl | yes refl
      = yes refl

  -- ### Matching

  module _
    {ss : Symbols}
    {vs : Variables}
    where

    record Match
      (r : Rule ss)
      (fs : Vec (Formula ss vs true) (arity r))
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
      : (r : Rule ss)
      → (fs : Vec (Formula ss vs true) (arity r))
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
        = Formula.substitutes-tail c hs subs p
      ; conclusion-valid
        = Formula.substitutes-head c hs subs p
      }

    ... | Formula.no p
      = no (λ {(match subs q r)
        → p (Formula.matches-with subs (Map.⊆-empty subs)
          (Formula.substitutes-cons c hs subs r q))})
  
    substitute-meta-match
      : {r : Rule ss}
      → {fs : Vec (Formula ss vs true) (arity r)}
      → {m : Meta}
      → {f' : Formula ss vs false}
      → {f : Formula ss vs true}
      → Match r fs f
      → Match r
        (Formula.substitutes-meta fs m f')
        (Formula.substitute-meta f m f')
    substitute-meta-match
      {r = rule _ _ hs c} {m = m} {f' = f'}
      (match subs p q)
      = record
      { substitutions
        = Formula.substitute-meta-substitutions subs m f'
      ; hypotheses-valid
        = Formula.substitutes-substitute-meta-substitutions hs subs m f' p
      ; conclusion-valid
        = Formula.substitute-substitute-meta-substitutions c subs m f' q
      }
  
-- ## Exports

open Rule public
  using (_≟_rul)

