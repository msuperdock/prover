module Examples where

open import Prover.Data.Any
  using (any)
open import Prover.Data.Associativity
  using (Associativity)
open import Prover.Data.Bool
  using (false)
open import Prover.Data.Empty
  using (⊥)
open import Prover.Data.Equal
  using (_≡_; refl)
open import Prover.Data.Formula
  using (Formula)
open import Prover.Data.Function
  using (_$_)
open import Prover.Data.If
  using (just; nothing)
open import Prover.Data.Maybe
  using (Maybe; just; nothing)
open import Prover.Data.Relation
  using (Dec; no; yes)
open import Prover.Data.Rule
  using (Rule)
open import Prover.Data.Rules
  using (Rules)
open import Prover.Data.String
  using (String)
open import Prover.Data.Symbol
  using (Symbol; both; left; neither)
open import Prover.Data.Symbols
  using (Symbols; sym_∈?_)
open import Prover.Data.Text
  using (Text)
open import Prover.Data.Token
  using (IsValid; Token; token)
open import Prover.Data.Unit
  using (⊤)
open import Prover.Data.Variable
  using (Variable)
open import Prover.Data.Variables
  using (Variables; var_∈?_)
open import Prover.Data.Vec
  using (Vec; []; _∷_)

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

is-nothing?
  : {A : Set}
  → (x : Maybe A)
  → Dec (x ≡ nothing)
is-nothing? nothing
  = yes refl
is-nothing? (just _)
  = no Maybe.just≢nothing

-- ## Text

text
  : String
  → Text
text
  = String.to-list

-- ## Symbol

-- Necessary because Char.is-space does not reduce.
postulate

  is-valid
    : (s : String)
    → IsValid (String.to-list s)

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
    = text "formula"
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
    = text "context"
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
    = text "turnstile"
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
    = text "empty"
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
    = text "comma"
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
    = text "and"
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
  = record
  { name
    = text "Γ"
  ; token
    = token' "Γ"
  }

⟨φ⟩
  : Variable
⟨φ⟩
  = record
  { name
    = text "φ"
  ; token
    = token' "φ"
  }

⟨ψ⟩
  : Variable
⟨ψ⟩
  = record
  { name
    = text "ψ"
  ; token
    = token' "ψ"
  }

-- ## Variables

variables-insert
  : (v : Variable)
  → (vs : Variables)
  → {_ : True (is-nothing? (Variables.lookup vs (Variable.name v)))}
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
    = text "and-formation"
  ; variables
    = ⟪φ,ψ⟫
  ; hypotheses
    = any
    $ φ formula
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
    = text "empty-formation"
  ; variables
    = ⟪⟫
  ; hypotheses
    = any
    $ []
  ; conclusion
    = ∅ context
  }

,-formation
  : Rule symbols
,-formation
  = record
  { name
    = text "comma-formation"
  ; variables
    = ⟪Γ,φ⟫
  ; hypotheses
    = any
    $ Γ context
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
    = text "axiom"
  ; variables
    = ⟪Γ,φ⟫
  ; hypotheses
    = any
    $ Γ context
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
    = text "weakening"
  ; variables
    = ⟪Γ,φ,ψ⟫
  ; hypotheses
    = any
    $ φ formula
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
    = text "and-introduction"
  ; variables
    = ⟪Γ,φ,ψ⟫
  ; hypotheses
    = any
    $ Γ ⊢ φ
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
    = text "and-elimination-left"
  ; variables
    = ⟪Γ,φ,ψ⟫
  ; hypotheses
    = any
    $ Γ ⊢ φ ∧ ψ
    ∷ []
  ; conclusion
    = Γ ⊢ φ
  }

∧-elimination-right
  : Rule symbols
∧-elimination-right
  = record
  { name
    = text "and-elimination-right"
  ; variables
    = ⟪Γ,φ,ψ⟫
  ; hypotheses
    = any
    $ Γ ⊢ φ ∧ ψ
    ∷ []
  ; conclusion
    = Γ ⊢ ψ
  }

∧-commutative
  : Rule symbols
∧-commutative
  = record
  { name
    = text "and-commutative"
  ; variables
    = ⟪φ,ψ⟫
  ; hypotheses
    = any
    $ φ formula
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

