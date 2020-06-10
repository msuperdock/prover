module Prover.Data.Formula where

open import Prover.Data.Identifier
  using (_≟_idn)
open import Prover.Data.Meta
  using (Meta; _≟_met)
open import Prover.Data.Metas
  using (Metas)
open import Prover.Data.Symbol
  using (Symbol; _≟_sym)
open import Prover.Data.Symbols
  using (Symbols; sym_∈_)
open import Prover.Data.Variable
  using (Variable; _≟_var)
open import Prover.Data.Variables
  using (Variables; var_∈_)
open import Prover.Prelude

open Map public
  using (_⊆_)

-- ## Definitions

module _Formula where

  data Formula
    (ss : Symbols)
    (vs : Variables)
    : Bool
    → Set
    where
  
    meta
      : (m : Meta)
      → Formula ss vs true
  
    variable'
      : {m : Bool}
      → (v : Variable)
      → .(var v ∈ vs)
      → Formula ss vs m
  
    symbol
      : {m : Bool}
      → {a : ℕ}
      → (s : Symbol a)
      → .(sym s ∈ ss)
      → Vec (Formula ss vs m) a
      → Formula ss vs m

Formula
  : Symbols
  → Variables
  → Bool
  → Set
Formula
  = _Formula.Formula

Substitutions
  : (ss : Symbols)
  → (vs : Variables)
  → Set
Substitutions ss vs
  = Map (Formula ss vs true) _≟_var

-- ## Module

module Formula where

  open _Formula.Formula public

  -- ### Metas

  module _
    {ss : Symbols}
    {vs : Variables}
    where

    metas-with
      : Formula ss vs true
      → Metas
      → Metas
    
    metas-withs
      : {n : ℕ}
      → Vec (Formula ss vs true) n
      → Metas
      → Metas
    
    metas-with (meta m) ms
      = Metas.insert ms m
    metas-with (variable' _ _)
      = id
    metas-with (symbol _ _ fs)
      = metas-withs fs
    
    metas-withs []
      = id
    metas-withs (f ∷ fs)
      = metas-withs fs
      ∘ metas-with f

  -- ### Completeness

  module _
    {ss : Symbols}
    {vs : Variables}
    where

    is-complete
      : Formula ss vs true
      → Bool
    
    are-complete
      : {n : ℕ}
      → Vec (Formula ss vs true) n
      → Bool
    
    is-complete (meta _)
      = false
    is-complete (variable' _ _)
      = true
    is-complete (symbol _ _ fs)
      = are-complete fs
    
    are-complete []
      = true
    are-complete (f ∷ fs)
      = is-complete f ∧ are-complete fs
    
    IsComplete
      : Formula ss vs true
      → Set
    IsComplete f
      = T (is-complete f)
    
    is-complete?
      : (f : Formula ss vs true)
      → Dec (IsComplete f)
    is-complete? f
      = Bool.to-dec (is-complete f)

    AreComplete
      : {n : ℕ}
      → Vec (Formula ss vs true) n
      → Set
    AreComplete fs
      = T (are-complete fs)

  -- ### Conversion

  module _
    {ss : Symbols}
    {vs : Variables}
    where

    from-meta-formula
      : (f : Formula ss vs true)
      → IsComplete f
      → Formula ss vs false
    
    from-meta-formulas
      : {n : ℕ}
      → (fs : Vec (Formula ss vs true) n)
      → AreComplete fs
      → Vec (Formula ss vs false) n
      
    from-meta-formula (variable' v p) _
      = variable' v p
    from-meta-formula (symbol s p fs) q
      = symbol s p (from-meta-formulas fs q)
    
    from-meta-formulas [] _
      = []
    from-meta-formulas (f ∷ fs) q
      = from-meta-formula f (Bool.∧-elimination-left q)
      ∷ from-meta-formulas fs (Bool.∧-elimination-right q)
    
    to-meta-formula
      : Formula ss vs false
      → Formula ss vs true
    
    to-meta-formulas
      : {n : ℕ}
      → Vec (Formula ss vs false) n
      → Vec (Formula ss vs true) n
    
    to-meta-formula (variable' v p)
      = variable' v p
    to-meta-formula (symbol s p fs)
      = symbol s p (to-meta-formulas fs)
    
    to-meta-formulas []
      = []
    to-meta-formulas (f ∷ fs)
      = to-meta-formula f ∷ to-meta-formulas fs
  
  -- ### Equality
  
  module _
    {ss : Symbols}
    {vs : Variables}
    {m : Bool}
    where

    _≟_frm
      : Decidable (Formula ss vs m)
    
    _≟_frms
      : {n : ℕ}
      → Decidable (Vec (Formula ss vs m) n)

    meta m₁ ≟ meta m₂ frm
      with m₁ ≟ m₂ met
    ... | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl
      = yes refl
    variable' v₁ _ ≟ variable' v₂ _ frm
      with v₁ ≟ v₂ idn
    ... | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl
      = yes refl
    symbol {a = n₁} s₁ _ fs₁ ≟ symbol {a = n₂} s₂ _ fs₂ frm
      with n₁ ≟ n₂ nat
    ... | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl
      with s₁ ≟ s₂ sym | fs₁ ≟ fs₂ frms
    ... | no ¬p | _
      = no (λ {refl → ¬p refl})
    ... | _ | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl | yes refl
      = yes refl

    meta _ ≟ variable' _ _ frm
      = no (λ ())
    meta _ ≟ symbol _ _ _ frm
      = no (λ ())
    variable' _ _ ≟ meta _ frm
      = no (λ ())
    variable' _ _ ≟ symbol _ _ _ frm
      = no (λ ())
    symbol _ _ _ ≟ meta _ frm
      = no (λ ())
    symbol _ _ _ ≟ variable' _ _ frm
      = no (λ ())
    
    [] ≟ [] frms
      = yes refl
    (x₁ ∷ xs₁) ≟ (x₂ ∷ xs₂) frms
      with x₁ ≟ x₂ frm | xs₁ ≟ xs₂ frms
    ... | no ¬p | _
      = no (λ {refl → ¬p refl})
    ... | _ | no ¬p
      = no (λ {refl → ¬p refl})
    ... | yes refl | yes refl
      = yes refl
  
  -- ### Membership
  
  module _
    {ss : Symbols}
    {vs : Variables}
    {m : Bool}
    {n : ℕ}
    where

    frm_∈_
      : Formula ss vs m
      → Vec (Formula ss vs m) n
      → Set
    frm f ∈ fs
      = Vec.IsMember fs f
    
    frm_∈?_
      : (f : Formula ss vs m)
      → (fs : Vec (Formula ss vs m) n)
      → Dec (frm f ∈ fs)
    frm f ∈? fs
      = Vec.is-member? _≟_frm fs f

  -- ### Properties

  module _
    {ss : Symbols}
    {vs : Variables}
    {a : ℕ}
    where

    symbol≢meta
      : (s : Symbol a)
      → .(p : sym s ∈ ss)
      → (fs : Vec (Formula ss vs true) a)
      → (m' : Meta)
      → symbol s p fs ≢ meta m'
    symbol≢meta _ _ _ _ ()
    
    symbol≢variable
      : {m : Bool}
      → (s : Symbol a)
      → .(p : sym s ∈ ss)
      → (fs : Vec (Formula ss vs m) a)
      → (v : Variable)
      → .(q : var v ∈ vs)
      → _≢_ {Formula ss vs m} (symbol s p fs) (variable' v q)
    symbol≢variable _ _ _ _ _ ()

  -- ### Substitution
  
  module _
    {ss : Symbols}
    {vs vs' : Variables}
    where

    substitute
      : Formula ss vs false
      → Substitutions ss vs'
      → Maybe (Formula ss vs' true)
    
    substitutes
      : {n : ℕ}
      → Vec (Formula ss vs false) n
      → Substitutions ss vs'
      → Maybe (Vec (Formula ss vs' true) n)
    
    substitute (variable' v _) subs
      = Map.lookup subs v
    substitute (symbol s p fs) subs
      with substitutes fs subs
    ... | just fs'
      = just (symbol s p fs')
    ... | nothing
      = nothing
    
    substitutes [] _
      = just []
    substitutes (f ∷ fs) subs
      with substitute f subs
      | substitutes fs subs
    ... | just f' | just fs'
      = just (f' ∷ fs')
    ... | _ | _
      = nothing

    ¬substitute-symbol-meta
      : {a : ℕ}
      → (s : Symbol a)
      → .(p : sym s ∈ ss)
      → (fs : Vec (Formula ss vs false) a)
      → (subs : Substitutions ss vs')
      → (m : Meta)
      → substitute (symbol s p fs) subs ≢ just (meta m)
    ¬substitute-symbol-meta s p fs subs m
      with substitutes fs subs
    ... | nothing
      = λ ()
    ... | just fs'
      = symbol≢meta s p fs' m
      ∘ Maybe.just-injective
    
    ¬substitute-symbol-variable
      : {a : ℕ}
      → (s : Symbol a)
      → .(p : sym s ∈ ss)
      → (fs : Vec (Formula ss vs false) a)
      → (subs : Substitutions ss vs')
      → (v : Variable)
      → .(q : var v ∈ vs')
      → substitute (symbol s p fs) subs ≢ just (variable' v q)
    ¬substitute-symbol-variable s p fs subs v q
      with substitutes fs subs
    ... | just fs'
      = symbol≢variable s p fs' v q
      ∘ Maybe.just-injective
    
    substitute-symbol-arity
      : {a a' : ℕ}
      → (s : Symbol a)
      → .(p : sym s ∈ ss)
      → (fs : Vec (Formula ss vs false) a)
      → (subs : Substitutions ss vs')
      → (s' : Symbol a')
      → .(p' : sym s' ∈ ss)
      → (fs' : Vec (Formula ss vs' true) a')
      → substitute (symbol s p fs) subs ≡ just (symbol s' p' fs')
      → a ≡ a'
    substitute-symbol-arity _ _ fs subs _ _ _ _
      with substitutes fs subs
    substitute-symbol-arity _ _ _ _ _ _ _ refl | just _
      = refl
    
    substitute-symbol-symbol 
      : {a : ℕ}
      → (s : Symbol a)
      → .(p : sym s ∈ ss)
      → (fs : Vec (Formula ss vs false) a)
      → (subs : Substitutions ss vs')
      → (s' : Symbol a)
      → .(p' : sym s' ∈ ss)
      → (fs' : Vec (Formula ss vs' true) a)
      → substitute (symbol s p fs) subs ≡ just (symbol s' p' fs')
      → s ≡ s'
    substitute-symbol-symbol _ _ fs subs _ _ _ _
      with substitutes fs subs
    substitute-symbol-symbol _ _ _ _ _ _ _ refl | just _
      = refl
    
    substitute-recursive
      : {a : ℕ}
      → (s : Symbol a)
      → .(p : sym s ∈ ss)
      → (fs : Vec (Formula ss vs false) a)
      → (subs : Substitutions ss vs')
      → (fs' : Vec (Formula ss vs' true) a)
      → substitutes fs subs ≡ just fs'
      → substitute (symbol s p fs) subs ≡ just (symbol s p fs')
    substitute-recursive _ _ fs subs _ _
      with substitutes fs subs
    substitute-recursive _ _ _ _ _ refl | _
      = refl
    
    substitutes-recursive
      : {n : ℕ}
      → (f : Formula ss vs false)
      → (fs : Vec (Formula ss vs false) n)
      → (subs : Substitutions ss vs')
      → (f' : Formula ss vs' true) 
      → (fs' : Vec (Formula ss vs' true) n)
      → substitute f subs ≡ just f'
      → substitutes fs subs ≡ just fs'
      → substitutes (f ∷ fs) subs ≡ just (f' ∷ fs')
    substitutes-recursive f fs subs _ _ _ _
      with substitute f subs
      | substitutes fs subs
    substitutes-recursive _ _ _ _ _ refl refl | _ | _
      = refl
    
    substitute-to-substitutes
      : {a : ℕ}
      → (s : Symbol a)
      → .(p : sym s ∈ ss)
      → (fs : Vec (Formula ss vs false) a)
      → (subs : Substitutions ss vs')
      → (fs' : Vec (Formula ss vs' true) a)
      → substitute (symbol s p fs) subs ≡ just (symbol s p fs')
      → substitutes fs subs ≡ just fs'
    substitute-to-substitutes _ _ fs subs _ _
      with substitutes fs subs
    substitute-to-substitutes _ _ _ _ _ refl | just _
      = refl
    
    substitutes-to-substitute
      : {n : ℕ}
      → (f : Formula ss vs false)
      → (fs : Vec (Formula ss vs false) n)
      → (subs : Substitutions ss vs')
      → (f' : Formula ss vs' true)
      → (fs' : Vec (Formula ss vs' true) n)
      → substitutes (f ∷ fs) subs ≡ just (f' ∷ fs')
      → substitute f subs ≡ just f'
    substitutes-to-substitute f fs subs _ _ _
      with substitute f subs
      | substitutes fs subs
    substitutes-to-substitute _ _ _ _ _ refl | just _ | just _
      = refl
    
    substitutes-to-substitutes
      : {n : ℕ}
      → (f : Formula ss vs false)
      → (fs : Vec (Formula ss vs false) n)
      → (subs : Substitutions ss vs')
      → (f' : Formula ss vs' true)
      → (fs' : Vec (Formula ss vs' true) n)
      → substitutes (f ∷ fs) subs ≡ just (f' ∷ fs')
      → substitutes fs subs ≡ just fs'
    substitutes-to-substitutes f fs subs _ _ _
      with substitute f subs
      | substitutes fs subs
    substitutes-to-substitutes _ _ _ _ _ refl | just _ | just _
      = refl
    
    substitute-⊆
      : (subs : Substitutions ss vs')
      → (subs' : Substitutions ss vs')
      → (f : Formula ss vs false)
      → (f' : Formula ss vs' true)
      → subs ⊆ subs'
      → substitute f subs ≡ just f'
      → substitute f subs' ≡ just f'
    
    substitutes-⊆
      : {n : ℕ}
      → (subs subs' : Substitutions ss vs')
      → (fs : Vec (Formula ss vs false) n)
      → (fs' : Vec (Formula ss vs' true) n)
      → subs ⊆ subs'
      → substitutes fs subs ≡ just fs'
      → substitutes fs subs' ≡ just fs'
    
    substitute-⊆ _ _ (variable' v _) f p q
      = p v f q
    substitute-⊆ subs subs' (symbol _ _ fs) f p q
      with substitutes fs subs
      | inspect (substitutes fs) subs
    ... | just fs' | [ r ]
      with substitutes fs subs'
      | substitutes-⊆ subs subs' fs fs' p r
    ... | _ | refl
      = q
    
    substitutes-⊆ _ _ [] [] _ _
      = refl
    substitutes-⊆ subs subs' (f ∷ fs) fs' p q
      with substitute f subs
      | inspect (substitute f) subs
      | substitutes fs subs
      | inspect (substitutes fs) subs
    ... | just f'' | [ r ] | just fs'' | [ rs ]
      with substitute f subs'
      | substitute-⊆ subs subs' f f'' p r
      | substitutes fs subs'
      | substitutes-⊆ subs subs' fs fs'' p rs
    ... | _ | refl | _ | refl
      = q

  -- ### Definite substitution

  module _
    {ss : Symbols}
    {vs vs' : Variables}
    where

    data SubstituteDefResult
      (f : Formula ss vs false)
      (subs : Substitutions ss vs')
      : Set
      where
      
      substitute-def-result
        : (f' : Formula ss vs' true)
        → (subs' : Substitutions ss vs')
        → Metas
        → subs ⊆ subs'
        → substitute f subs' ≡ just f'
        → SubstituteDefResult f subs
    
    data SubstitutesDefResult
      {n : ℕ}
      (fs : Vec (Formula ss vs false) n)
      (subs : Substitutions ss vs')
      : Set
      where
    
      substitutes-def-result
        : (fs' : Vec (Formula ss vs' true) n)
        → (subs' : Substitutions ss vs')
        → Metas
        → subs ⊆ subs'
        → substitutes fs subs' ≡ just fs'
        → SubstitutesDefResult fs subs
    
    -- Perform substitution, replacing undetermined variables with metas.
    substitute-def
      : (f : Formula ss vs false)
      → (subs : Substitutions ss vs')
      → Metas
      → SubstituteDefResult f subs
    
    -- Perform substitution, replacing undetermined variables with metas.
    substitutes-def
      : {n : ℕ}
      → (fs : Vec (Formula ss vs false) n)
      → (subs : Substitutions ss vs')
      → Metas
      → SubstitutesDefResult fs subs
    
    substitute-def (variable' v _) subs ms
      with Map.lookup subs v
      | inspect (Map.lookup subs) v
      | Metas.fresh ms
    
    ... | nothing | [ p ] | (m , ms')
      = substitute-def-result (meta m) (Map.insert subs v (meta m) p) ms'
          (Map.⊆-insert subs subs v (meta m) p (Map.⊆-reflexive subs))
          (Map.lookup-insert subs v (meta m) p)
    
    ... | just f | [ p ] | _
      = substitute-def-result f subs ms (Map.⊆-reflexive subs) p
    
    substitute-def (symbol s p fs) subs ms
      with substitutes-def fs subs ms
    
    ... | substitutes-def-result fs' subs' ms' q r
      = substitute-def-result (symbol s p fs') subs' ms' q
        (substitute-recursive s p fs subs' fs' r)
    
    substitutes-def [] subs ms
      = substitutes-def-result [] subs ms (Map.⊆-reflexive subs) refl
    
    substitutes-def (f ∷ fs) subs ms
      with substitute-def f subs ms
    ... | substitute-def-result f' subs' ms' p q
      with substitutes-def fs subs' ms'
    ... | substitutes-def-result fs' subs'' ms'' ps qs
      = substitutes-def-result (f' ∷ fs') subs'' ms''
        (Map.⊆-transitive subs subs' subs'' p ps)
        (substitutes-recursive f fs subs'' f' fs'
          (substitute-⊆ subs' subs'' f f' ps q) qs)

  -- ### Meta-substitution

  module _
    {ss : Symbols}
    where

    substitute-meta
      : {vs : Variables}
      → Formula ss vs true
      → Meta
      → Formula ss vs false
      → Formula ss vs true
    
    substitutes-meta
      : {vs : Variables}
      → {n : ℕ}
      → Vec (Formula ss vs true) n
      → Meta
      → Formula ss vs false
      → Vec (Formula ss vs true) n
    
    substitute-meta (symbol s p fs) m f'
      = symbol s p (substitutes-meta fs m f')
    substitute-meta f@(variable' _ _) _ _
      = f
    substitute-meta f@(meta m') m f'
      with m ≟ m' met
    ... | no _
      = f
    ... | yes _
      = to-meta-formula f'
    
    substitutes-meta [] _ _
      = []
    substitutes-meta (f ∷ fs) m f'
      = substitute-meta f m f'
      ∷ substitutes-meta fs m f'
    
    substitute-meta-to-meta-formula
      : {vs : Variables}
      → (f : Formula ss vs false)
      → (m : Meta)
      → (f' : Formula ss vs false)
      → substitute-meta (to-meta-formula f) m f' ≡ to-meta-formula f
    
    substitute-meta-to-meta-formulas
      : {vs : Variables}
      → {n : ℕ}
      → (fs : Vec (Formula ss vs false) n)
      → (m : Meta)
      → (f' : Formula ss vs false)
      → substitutes-meta (to-meta-formulas fs) m f' ≡ to-meta-formulas fs
    
    substitute-meta-to-meta-formula (variable' _ _) _ _
      = refl
    substitute-meta-to-meta-formula (symbol s p fs) m f'
      = sub (symbol s p) (substitute-meta-to-meta-formulas fs m f')
    
    substitute-meta-to-meta-formulas [] _ _
      = refl
    substitute-meta-to-meta-formulas (f ∷ fs) m f'
      = Vec.cons-eq
        (substitute-meta-to-meta-formula f m f')
        (substitute-meta-to-meta-formulas fs m f')
    
    substitute-meta-substitutions
      : {vs : Variables}
      → Substitutions ss vs
      → Meta
      → Formula ss vs false
      → Substitutions ss vs
    substitute-meta-substitutions subs m f
      = Map.map (λ f' → substitute-meta f' m f) subs
    
    substitute-substitute-meta-substitutions
      : {vs vs' : Variables}
      → (f : Formula ss vs false)
      → (subs : Substitutions ss vs')
      → (m : Meta)
      → (f'' : Formula ss vs' false)
      → (f' : Formula ss vs' true)
      → substitute f subs ≡ just f'
      → substitute f (substitute-meta-substitutions subs m f'')
        ≡ just (substitute-meta f' m f'')
    
    substitutes-substitute-meta-substitutions
      : {vs vs' : Variables}
      → {n : ℕ}
      → (fs : Vec (Formula ss vs false) n)
      → (subs : Substitutions ss vs')
      → (m : Meta)
      → (f'' : Formula ss vs' false)
      → (fs' : Vec (Formula ss vs' true) n)
      → substitutes fs subs ≡ just fs'
      → substitutes fs (substitute-meta-substitutions subs m f'')
        ≡ just (substitutes-meta fs' m f'')
    
    substitute-substitute-meta-substitutions (variable' v _) subs m f'' f' p
      = Map.lookup-map (λ x → substitute-meta x m f'') subs v f' p
    
    substitute-substitute-meta-substitutions (symbol _ _ fs) subs _ _ _ _
      with substitutes fs subs
      | inspect (substitutes fs) subs
    substitute-substitute-meta-substitutions (symbol _ _ fs) subs m f'' _ refl
      | just fs' | [ p ]
      with substitutes fs (substitute-meta-substitutions subs m f'')
      | substitutes-substitute-meta-substitutions fs subs m f'' fs' p
    ... | _ | refl
      = refl
    
    substitutes-substitute-meta-substitutions [] _ _ _ [] _
      = refl
    substitutes-substitute-meta-substitutions (f ∷ fs) subs _ _ _ _
      with substitute f subs
      | inspect (substitute f) subs
      | substitutes fs subs
      | inspect (substitutes fs) subs
    substitutes-substitute-meta-substitutions
      (f ∷ fs) subs m f'' (f' ∷ fs') refl
      | just _ | [ p ] | just _ | [ ps ]
      with substitute f (substitute-meta-substitutions subs m f'')
      | substitute-substitute-meta-substitutions f subs m f'' f' p
      | substitutes fs (substitute-meta-substitutions subs m f'')
      | substitutes-substitute-meta-substitutions fs subs m f'' fs' ps
    ... | _ | refl | _ | refl
      = refl

  -- ### Matching

  module _
    {ss : Symbols}
    {vs vs' : Variables}
    where

    record Match
      (f : Formula ss vs false)
      (f' : Formula ss vs' true)
      : Set
      where
  
      constructor
      
        match
  
      field
  
        substitutions
          : Substitutions ss vs'
  
        valid
          : substitute f substitutions ≡ just f'
  
    record MatchWith
      (subs : Substitutions ss vs')
      (f : Formula ss vs false)
      (f' : Formula ss vs' true)
      : Set
      where
  
      constructor
      
        match-with
  
      field
  
        substitutions
          : Substitutions ss vs'
  
        subset
          : subs ⊆ substitutions
  
        valid
          : substitute f substitutions ≡ just f'
      
    record MatchesWith
      {n : ℕ}
      (subs : Substitutions ss vs')
      (fs : Vec (Formula ss vs false) n)
      (fs' : Vec (Formula ss vs' true) n)
      : Set
      where
  
      constructor
      
        matches-with
  
      field
  
        substitutions
          : Substitutions ss vs'
  
        subset
          : subs ⊆ substitutions
  
        valid
          : substitutes fs substitutions ≡ just fs'
    
    record MatchWithMinimal
      (subs : Substitutions ss vs')
      (f : Formula ss vs false)
      (f' : Formula ss vs' true)
      : Set
      where
  
      constructor
      
        match-with-minimal
  
      field
  
        substitutions
          : Substitutions ss vs'
  
        subset
          : subs ⊆ substitutions
  
        valid
          : substitute f substitutions ≡ just f'
  
        minimal
          : (m : MatchWith subs f f')
          → substitutions ⊆ MatchWith.substitutions m
  
    record MatchesWithMinimal
      {n : ℕ}
      (subs : Substitutions ss vs')
      (fs : Vec (Formula ss vs false) n)
      (fs' : Vec (Formula ss vs' true) n)
      : Set
      where
  
      constructor
      
        matches-with-minimal
  
      field
  
        substitutions
          : Substitutions ss vs'
  
        subset
          : subs ⊆ substitutions
  
        valid
          : substitutes fs substitutions ≡ just fs'
  
        minimal
          : (m : MatchesWith subs fs fs')
          → substitutions ⊆ MatchesWith.substitutions m
    
    data MatchWith?
      (subs : Substitutions ss vs')
      (f : Formula ss vs false)
      (f' : Formula ss vs' true)
      : Set
      where
    
      yes
        : MatchWithMinimal subs f f'
        → MatchWith? subs f f'
  
      no
        : ¬ MatchWith subs f f'
        → MatchWith? subs f f'
    
    data MatchesWith?
      {n : ℕ}
      (subs : Substitutions ss vs')
      (fs : Vec (Formula ss vs false) n)
      (fs' : Vec (Formula ss vs' true) n)
      : Set
      where
    
      yes
        : MatchesWithMinimal subs fs fs'
        → MatchesWith? subs fs fs'
  
      no
        : ¬ MatchesWith subs fs fs'
        → MatchesWith? subs fs fs'
    
    match-to-matches
      : {a : ℕ}
      → (subs : Substitutions ss vs')
      → (s : Symbol a)
      → .(p : sym s ∈ ss)
      → (fs : Vec (Formula ss vs false) a)
      → (fs' : Vec (Formula ss vs' true) a)
      → MatchWith subs (symbol s p fs) (symbol s p fs')
      → MatchesWith subs fs fs'
    match-to-matches subs s p fs fs' (match-with subs' q r)
      = matches-with subs' q (substitute-to-substitutes s p fs subs' fs' r)
    
    matches-to-match
      : {n : ℕ}
      → (subs : Substitutions ss vs')
      → (f : Formula ss vs false)
      → (fs : Vec (Formula ss vs false) n)
      → (f' : Formula ss vs' true)
      → (fs' : Vec (Formula ss vs' true) n)
      → MatchesWith subs (f ∷ fs) (f' ∷ fs')
      → MatchWith subs f f'
    matches-to-match subs f fs f' fs' (matches-with subs' p q)
      = match-with subs' p (substitutes-to-substitute f fs subs' f' fs' q)
    
    matches-to-matches
      : {n : ℕ}
      → (subs : Substitutions ss vs')
      → (f : Formula ss vs false)
      → (fs : Vec (Formula ss vs false) n)
      → (f' : Formula ss vs' true)
      → (fs' : Vec (Formula ss vs' true) n)
      → (m : MatchWithMinimal subs f f')
      → MatchesWith subs (f ∷ fs) (f' ∷ fs')
      → MatchesWith (MatchWithMinimal.substitutions m) fs fs'
    matches-to-matches subs f fs f' fs'
      (match-with-minimal subs' p _ r)
      m@(matches-with subs'' p' qs)
      = matches-with subs'' (r (matches-to-match subs f fs f' fs' m))
        (substitutes-to-substitutes f fs subs'' f' fs' qs)
    
    insert-minimal
      : (subs : Substitutions ss vs')
      → (v : Variable)
      → .(p : var v ∈ vs)
      → (f : Formula ss vs' true)
      → (q : Map.lookup subs v ≡ nothing)
      → (m : MatchWith subs (variable' v p) f)
      → Map.insert subs v f q ⊆ MatchWith.substitutions m
    insert-minimal subs v _ f p (match-with _ q _) w f' r
      with w ≟ v var
    ... | no ¬p
      with Map.lookup (Map.insert subs v f p) w
      | Map.lookup-other subs v f p w ¬p
    ... | _ | refl
      = q w f' r
    insert-minimal _ _ _ _ _ (match-with _ _ p) _ _ refl | yes refl
      = p
    
    match-with?
      : (subs : Substitutions ss vs')
      → (f : Formula ss vs false)
      → (f' : Formula ss vs' true)
      → MatchWith? subs f f'
    
    matches-with?
      : {n : ℕ}
      → (subs : Substitutions ss vs')
      → (fs : Vec (Formula ss vs false) n)
      → (fs' : Vec (Formula ss vs' true) n)
      → MatchesWith? subs fs fs'
    
    match-with? subs (variable' v p) f
      with Map.lookup subs v
      | inspect (Map.lookup subs) v 
    
    ... | nothing | [ q ]
      = yes (match-with-minimal
        (Map.insert subs v f q)
        (Map.⊆-insert subs subs v f q (Map.⊆-reflexive subs))
        (Map.lookup-insert subs v f q)
        (insert-minimal subs v p f q))
    ... | just f' | [ q ]
      with f ≟ f' frm
    
    ... | no r
      = no (λ {(match-with subs' s t)
        → r (Maybe.just-injective (trans (sym t) (s v f' q)))})
    ... | yes refl
      = yes (match-with-minimal subs (Map.⊆-reflexive subs) q
        (λ {(match-with subs' p _) w f' s → p w f' s}))
    
    match-with? _ (symbol s p fs) (meta m)
      = no (λ {(match-with subs _ q)
        → (¬substitute-symbol-meta s p fs subs m q)})
    
    match-with? _ (symbol s p fs) (variable' v q)
      = no (λ {(match-with subs _ r)
        → (¬substitute-symbol-variable s p fs subs v q r)})
    
    match-with? subs (symbol {a = a} s p fs) (symbol {a = a'} s' p' fs')
      with a ≟ a' nat
    
    ... | no ¬p
      = no (λ {(match-with subs' _ r)
        → ¬p (substitute-symbol-arity s p fs subs' s' p' fs' r)})
    ... | yes refl
      with s ≟ s' sym
    
    ... | no ¬p
      = no (λ {(match-with subs' _ r)
        → ¬p (substitute-symbol-symbol s p fs subs' s' p' fs' r)})
    ... | yes refl
      with matches-with? subs fs fs'
    
    ... | no ¬p
      = no (¬p ∘ match-to-matches subs s p fs fs')
    ... | yes (matches-with-minimal subs' p'' q'' r'')
      = yes (match-with-minimal subs' p''
        (substitute-recursive s p fs subs' fs' q'')
        (λ {(match-with subs'' q''' r''')
          → r'' (matches-with subs'' q'''
            (substitute-to-substitutes s p fs subs'' fs' r'''))}))
    
    matches-with? subs [] []
      = yes (matches-with-minimal subs (Map.⊆-reflexive subs) refl
        (λ {(matches-with subs' p _) v f q → p v f q}))
    
    matches-with? subs (f ∷ fs) (f' ∷ fs')
      with match-with? subs f f'
    
    ... | no ¬p
      = no (¬p ∘ matches-to-match subs f fs f' fs')
    ... | yes m@(match-with-minimal subs' p q r)
      with matches-with? subs' fs fs'
    
    ... | no ¬p
      = no (λ {m' → ¬p (matches-to-matches subs f fs f' fs' m m')})
    ... | yes (matches-with-minimal subs'' p' q' r')
      = yes (matches-with-minimal subs''
        (Map.⊆-transitive subs subs' subs'' p p')
        (substitutes-recursive f fs subs'' f' fs'
          (substitute-⊆ subs' subs'' f f' p' q) q')
        (λ {(matches-with subs''' p'' q'')
          → r' (matches-with subs'''
            (r (match-with subs''' p''
              (substitutes-to-substitute f fs subs''' f' fs' q'')))
            (substitutes-to-substitutes f fs subs''' f' fs' q''))}))
    
    match?
      : (f : Formula ss vs false)
      → (f' : Formula ss vs' true)
      → Dec (Match f f')
    match? f f'
      with match-with? Map.empty f f'
    ... | yes (match-with-minimal subs _ p _)
      = yes (match subs p)
    ... | no ¬p
      = no (λ {(match subs q) → ¬p (match-with subs (Map.⊆-empty subs) q)})
  
-- ## Exports

open Formula public
  using (_≟_frm; _≟_frms; frm_∈_; frm_∈?_)

