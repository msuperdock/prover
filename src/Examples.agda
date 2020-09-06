module Examples where

open import Prover.Data.Associativity
  using (Associativity)
open import Prover.Data.Identifier
  using (Identifier)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Rule
  using (Rule)
open import Prover.Data.Rules
  using (Rules)
open import Prover.Data.Symbol
  using (Symbol; both; left; neither)
open import Prover.Data.Symbols
  using (Symbols; sym_∈?_)
open import Prover.Data.Token
  using (Token; token)
open import Prover.Data.Variable
  using (Variable)
open import Prover.Data.Variables
  using (Variables; var_∈?_)
open import Prover.Prelude
  hiding (_,_; _∧_)

open Vec
  using ([]; _∷_)

-- ## Utilities

True
  : {P : Set}
  → Dec P
  → Set
True (no _)
  = ⊥
True (yes _)
  = ⊤

to-witness
  : {P : Set}
  → {p : Dec P}
  → True p
  → P
to-witness {p = yes p} _
  = p

is-false?
  : (x : Bool)
  → Dec (x ≡ false)
is-false? false
  = yes refl
is-false? true
  = no (λ ())

is-nothing?
  : {A : Set}
  → (x : Maybe A)
  → Dec (x ≡ nothing)
is-nothing? nothing
  = yes refl
is-nothing? (just _)
  = no Maybe.just≢nothing

-- ## Identifier

NonEmpty
  : String
  → Set
NonEmpty s
  with String.to-list s
... | any Vec.nil
  = ⊥
... | any (Vec.cons _ _)
  = ⊤

identifier'
  : (n : String)
  → {_ : NonEmpty n}
  → Identifier
identifier' n
  with String.to-list n
... | any cs@(Vec.cons _ _)
  = any cs

-- ## Symbol

-- Necessary because Char.is-space does not reduce.
postulate

  is-valid
    : (s : String)
    → Token.IsValid (String.to-list s)

token'
  : String
  → Token
token' s
  = token (String.to-list s) (is-valid s)

⟨formula⟩
  : Symbol
⟨formula⟩
  = record
  { valid
    = left
  ; name
    = identifier' "formula"
  ; tokens
    = token' " formula" ∷ []
  ; precedence
    = just 0
  ; associativity
    = nothing
  }

⟨context⟩
  : Symbol
⟨context⟩
  = record
  { valid
    = left
  ; name
    = identifier' "context"
  ; tokens
    = token' " context" ∷ []
  ; precedence
    = just 0
  ; associativity
    = nothing
  }

⟨⊢⟩
  : Symbol
⟨⊢⟩
  = record
  { valid
    = both
  ; name
    = identifier' "turnstile"
  ; tokens
    = token' " ⊢ " ∷ []
  ; precedence
    = just 0
  ; associativity
    = just Associativity.left
  }

⟨∅⟩
  : Symbol
⟨∅⟩
  = record
  { valid
    = neither
  ; name
    = identifier' "empty"
  ; tokens
    = token' "∅" ∷ []
  ; precedence
    = nothing
  ; associativity
    = nothing
  }

⟨,⟩
  : Symbol
⟨,⟩
  = record
  { valid
    = both
  ; name
    = identifier' "comma"
  ; tokens
    = token' ", " ∷ []
  ; precedence
    = just 1
  ; associativity
    = just Associativity.right
  }

⟨∧⟩
  : Symbol
⟨∧⟩
  = record
  { valid
    = both
  ; name
    = identifier' "and"
  ; tokens
    = token' " ∧ " ∷ []
  ; precedence
    = just 2
  ; associativity
    = just Associativity.right
  }

-- ## Symbols

symbols-insert
  : (s : Symbol)
  → (ss : Symbols)
  → {_ : True (is-nothing? (Symbols.lookup ss (Symbol.name s)))}
  → Symbols
symbols-insert s ss {p}
  = Symbols.insert ss s (to-witness p)

symbols
  : Symbols
symbols
  = symbols-insert ⟨formula⟩
  $ symbols-insert ⟨context⟩
  $ symbols-insert ⟨⊢⟩
  $ symbols-insert ⟨∅⟩
  $ symbols-insert ⟨,⟩
  $ symbols-insert ⟨∧⟩
  $ Symbols.empty

-- ## Variable

⟨Γ⟩
  : Variable
⟨Γ⟩
  = identifier' "g"

⟨φ⟩
  : Variable
⟨φ⟩
  = identifier' "p"

⟨ψ⟩
  : Variable
⟨ψ⟩
  = identifier' "q"

-- ## Variables

variables-insert
  : (v : Variable)
  → (vs : Variables)
  → {_ : True (is-false? (Variables.is-member vs v))}
  → Variables
variables-insert v vs {p}
  = Variables.insert vs v (to-witness p)

⟪⟫
  : Variables
⟪⟫
  = Variables.empty

⟪Γ,φ⟫
  : Variables
⟪Γ,φ⟫
  = variables-insert ⟨Γ⟩
  $ variables-insert ⟨φ⟩
  $ Variables.empty

⟪φ,ψ⟫
  : Variables
⟪φ,ψ⟫
  = variables-insert ⟨φ⟩
  $ variables-insert ⟨ψ⟩
  $ Variables.empty

⟪Γ,φ,ψ⟫
  : Variables
⟪Γ,φ,ψ⟫
  = variables-insert ⟨Γ⟩
  $ variables-insert ⟨φ⟩
  $ variables-insert ⟨ψ⟩
  $ Variables.empty

-- ## Formula

formula-variable
  : {vs : Variables}
  → (v  : Variable)
  → {_ : True (var v ∈? vs)}
  → Formula symbols vs false
formula-variable v {p}
  = Formula.variable' v (to-witness p)

formula-symbol
  : {vs : Variables}
  → (s : Symbol)
  → {_ : True (sym s ∈? symbols)}
  → Vec (Formula symbols vs false) (Symbol.arity s)
  → Formula symbols vs false
formula-symbol s {p}
  = Formula.symbol s (to-witness p)

φ
  : {vs : Variables}
  → {_ : True (var ⟨φ⟩ ∈? vs)}
  → Formula symbols vs false
φ {_} {p}
  = formula-variable ⟨φ⟩ {p}

ψ
  : {vs : Variables}
  → {_ : True (var ⟨ψ⟩ ∈? vs)}
  → Formula symbols vs false
ψ {_} {p}
  = formula-variable ⟨ψ⟩ {p}

Γ
  : {vs : Variables}
  → {_ : True (var ⟨Γ⟩ ∈? vs)}
  → Formula symbols vs false
Γ {_} {p}
  = formula-variable ⟨Γ⟩ {p}

infix 30 _formula
infix 30 _context
infix 30 _⊢_
infixr 40 _,_
infixl 50 _∧_

_formula
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
_formula f₀
  = formula-symbol ⟨formula⟩ (f₀ ∷ [])

_context
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
_context f₀
  = formula-symbol ⟨context⟩ (f₀ ∷ [])

_⊢_
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
  → Formula symbols vs false
_⊢_ f₀ f₁
  = formula-symbol ⟨⊢⟩ (f₀ ∷ f₁ ∷ [])

∅
  : {vs : Variables}
  → Formula symbols vs false
∅
  = formula-symbol ⟨∅⟩ []

_,_
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
  → Formula symbols vs false
_,_ f₀ f₁
  = formula-symbol ⟨,⟩ (f₀ ∷ f₁ ∷ [])

_∧_
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
  → Formula symbols vs false
_∧_ f₀ f₁
  = formula-symbol ⟨∧⟩ (f₀ ∷ f₁ ∷ [])

-- ## Rule

∧-formation
  : Rule symbols
∧-formation
  = record
  { name
    = identifier' "and-formation"
  ; variables
    = ⟪φ,ψ⟫
  ; hypotheses
    = φ formula
    ∷ ψ formula
    ∷ []
  ; conclusion
    = φ ∧ ψ formula
  }

∅-formation
  : Rule symbols
∅-formation
  = record
  { name
    = identifier' "empty-formation"
  ; variables
    = ⟪⟫
  ; hypotheses
    = []
  ; conclusion
    = ∅ context
  }

,-formation
  : Rule symbols
,-formation
  = record
  { name
    = identifier' "comma-formation"
  ; variables
    = ⟪Γ,φ⟫
  ; hypotheses
    = Γ context
    ∷ φ formula
    ∷ []
  ; conclusion
    = φ , Γ context
  }

axiom
  : Rule symbols
axiom
  = record
  { name
    = identifier' "axiom"
  ; variables
    = ⟪Γ,φ⟫
  ; hypotheses
    = Γ context
    ∷ φ formula
    ∷ []
  ; conclusion
    = φ , Γ ⊢ φ
  }

weakening
  : Rule symbols
weakening
  = record
  { name
    = identifier' "weakening"
  ; variables
    = ⟪Γ,φ,ψ⟫
  ; hypotheses
    = φ formula
    ∷ Γ ⊢ ψ
    ∷ []
  ; conclusion
    = φ , Γ ⊢ ψ
  }

∧-introduction
  : Rule symbols
∧-introduction
  = record
  { name
    = identifier' "and-introduction"
  ; variables
    = ⟪Γ,φ,ψ⟫
  ; hypotheses
    = Γ ⊢ φ
    ∷ Γ ⊢ ψ
    ∷ []
  ; conclusion
    = Γ ⊢ φ ∧ ψ
  }

∧-elimination-left
  : Rule symbols
∧-elimination-left
  = record
  { name
    = identifier' "and-elimination-left"
  ; variables
    = ⟪Γ,φ,ψ⟫
  ; hypotheses
    = Γ ⊢ φ ∧ ψ
    ∷ []
  ; conclusion
    = Γ ⊢ φ
  }

∧-elimination-right
  : Rule symbols
∧-elimination-right
  = record
  { name
    = identifier' "and-elimination-right"
  ; variables
    = ⟪Γ,φ,ψ⟫
  ; hypotheses
    = Γ ⊢ φ ∧ ψ
    ∷ []
  ; conclusion
    = Γ ⊢ ψ
  }

∧-commutative
  : Rule symbols
∧-commutative
  = record
  { name
    = identifier' "and-commutative"
  ; variables
    = ⟪φ,ψ⟫
  ; hypotheses
    = φ formula
    ∷ ψ formula
    ∷ []
  ; conclusion
    = φ ∧ ψ , ∅ ⊢ ψ ∧ φ
  }

-- ## Rules

rules-insert
  : (r : Rule symbols)
  → (rs : Rules symbols)
  → {_ : True (is-nothing? (Rules.lookup rs (Rule.name r)))}
  → Rules symbols
rules-insert r rs {p}
  = Rules.insert rs r (to-witness p)

rules
  : Rules symbols
rules
  = rules-insert ∧-formation
  $ rules-insert ∅-formation
  $ rules-insert ,-formation
  $ rules-insert axiom
  $ rules-insert weakening
  $ rules-insert ∧-introduction
  $ rules-insert ∧-elimination-left
  $ rules-insert ∧-elimination-right
  $ Rules.empty

