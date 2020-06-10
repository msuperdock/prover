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
  using (Symbol; both; left; neither; right)
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
is-nothing? (just x)
  = no (Maybe.just≢nothing x)

-- ## Identifier

NonEmpty
  : String
  → Set
NonEmpty s
  with String.to-vec s
... | any []
  = ⊥
... | any (_ ∷ _)
  = ⊤

identifier'
  : (n : String)
  → {p : NonEmpty n}
  → Identifier
identifier' n {p = p}
  with String.to-vec n
... | any cs@(_ ∷ _)
  = any cs

-- ## Symbol

-- Necessary because Char.is-space does not reduce.
postulate

  is-valid
    : (s : String)
    → Token.IsValid (Any.value (String.to-vec s))

token'
  : String
  → Token
token' s
  = token (Any.value (String.to-vec s)) (is-valid s)

⟨formula⟩
  : Symbol 1
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
  : Symbol 1
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
  : Symbol 2
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
  : Symbol 0
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
  : Symbol 2
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
  : Symbol 2
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
  : {a : ℕ}
  → (s : Symbol a)
  → (ss : Symbols)
  → {p : True (is-nothing? (Symbols.lookup ss (Symbol.name s)))}
  → Symbols
symbols-insert s ss {p = p}
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
  → {p : True (is-false? (Variables.is-member vs v))}
  → Variables
variables-insert v vs {p = p}
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
  → {p : True (var v ∈? vs)}
  → Formula symbols vs false
formula-variable v {p = p}
  = Formula.variable' v (to-witness p)

formula-symbol
  : {vs : Variables}
  → {a : ℕ}
  → (s : Symbol a)
  → {p : True (sym s ∈? symbols)}
  → Vec (Formula symbols vs false) a
  → Formula symbols vs false
formula-symbol s {p = p}
  = Formula.symbol s (to-witness p)

formula₀
  : {vs : Variables}
  → (s : Symbol 0)
  → {p : True (sym s ∈? symbols)}
  → Formula symbols vs false
formula₀ s {p = p}
  = formula-symbol s {p = p} []

formula₁
  : {vs : Variables}
  → (s : Symbol 1)
  → {p : True (sym s ∈? symbols)}
  → Formula symbols vs false
  → Formula symbols vs false
formula₁ s {p = p} f₁
  = formula-symbol s {p = p} (f₁ ∷ [])

formula₂
  : {vs : Variables}
  → (s : Symbol 2)
  → {p : True (sym s ∈? symbols)}
  → Formula symbols vs false
  → Formula symbols vs false
  → Formula symbols vs false
formula₂ s {p = p} f₁ f₂
  = formula-symbol s {p = p} (f₁ ∷ f₂ ∷ [])

φ
  : {vs : Variables}
  → {p : True (var ⟨φ⟩ ∈? vs)}
  → Formula symbols vs false
φ {p = p}
  = formula-variable ⟨φ⟩ {p = p}

ψ
  : {vs : Variables}
  → {p : True (var ⟨ψ⟩ ∈? vs)}
  → Formula symbols vs false
ψ {p = p}
  = formula-variable ⟨ψ⟩ {p = p}

Γ
  : {vs : Variables}
  → {p : True (var ⟨Γ⟩ ∈? vs)}
  → Formula symbols vs false
Γ {p = p}
  = formula-variable ⟨Γ⟩ {p = p}

infix 30 _formula
infix 30 _context
infix 30 _⊢_
infixr 40 _,_
infixl 50 _∧_

_formula
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
_formula
  = formula₁ ⟨formula⟩

_context
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
_context
  = formula₁ ⟨context⟩

_⊢_
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
  → Formula symbols vs false
_⊢_
  = formula₂ ⟨⊢⟩

∅
  : {vs : Variables}
  → Formula symbols vs false
∅
  = formula₀ ⟨∅⟩

_,_
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
  → Formula symbols vs false
_,_
  = formula₂ ⟨,⟩

_∧_
  : {vs : Variables}
  → Formula symbols vs false
  → Formula symbols vs false
  → Formula symbols vs false
_∧_
  = formula₂ ⟨∧⟩

-- ## Rule

∧-formation
  : Rule symbols 2
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
  : Rule symbols 0
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
  : Rule symbols 2
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
  : Rule symbols 2
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
  : Rule symbols 2
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
  : Rule symbols 2
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
  : Rule symbols 1
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
  : Rule symbols 1
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
  : Rule symbols 2
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
  : {a : ℕ}
  → (r : Rule symbols a)
  → (rs : Rules symbols)
  → {p : True (is-nothing? (Rules.lookup rs (Rule.name r)))}
  → Rules symbols
rules-insert r rs {p = p}
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
