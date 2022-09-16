module Prover.Data.Rule where

open import Prover.Data.Any
  using (any)
open import Prover.Data.Bool
  using (false; true)
open import Prover.Data.Equal
  using (Equal; _≡_; refl)
open import Prover.Data.Formula
  using (Formula; Substitutions; _≟_frm; _≟_frms')
open import Prover.Data.Function
  using (_$_)
open import Prover.Data.List
  using (List)
open import Prover.Data.Map
  using (Map)
open import Prover.Data.Maybe
  using (just)
open import Prover.Data.Meta
  using (Meta)
open import Prover.Data.Nat
  using (ℕ)
open import Prover.Data.Relation
  using (Dec; Decidable; no; yes)
open import Prover.Data.Symbols
  using (Symbols)
open import Prover.Data.Text
  using (Text; _≟_txt)
open import Prover.Data.Variables
  using (Variables; _≟_vars)
open import Prover.Data.Vec
  using (Vec; _∷_)

-- ## Definition

record Rule'
  (ss : Symbols)
  : Set
  where

  constructor
  
    rule

  field

    name
      : Text

    variables
      : Variables

    hypotheses
      : List (Formula ss variables false)

    conclusion
      : Formula ss variables false

  arity
    : ℕ
  arity
    = List.length hypotheses

  hypotheses-vec
    : Vec (Formula ss variables false) arity
  hypotheses-vec
    = List.to-vec hypotheses

Rule
  = Rule'

-- ## Module

module Rule where

  open Rule' public

  -- ### Equality

  module _
    {ss : Symbols}
    where

    _≟_rul
      : Decidable (Equal (Rule ss))
    rule n₁ vs₁ hs₁ c₁ ≟ rule n₂ vs₂ hs₂ c₂ rul
      with n₁ ≟ n₂ txt
      | vs₁ ≟ vs₂ vars
  
    ... | no ¬p | _
      = no (λ {refl → ¬p refl})
    ... | _ | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl | yes refl
      with hs₁ ≟ hs₂ frms'
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
          : Formula.substitutes (hypotheses-vec r) substitutions ≡ just fs
  
        conclusion-valid
          : Formula.substitute (conclusion r) substitutions ≡ just f
  
    match?
      : (r : Rule ss)
      → (fs : Vec (Formula ss vs true) (arity r))
      → (f : Formula ss vs true)
      → Dec (Match r fs f)
    match? (rule _ _ (any hs) c) fs f
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
      {r = rule _ _ (any hs) c} {m = m} {f' = f'}
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

