module Prover.Prelude.Collection where

open import Prover.Prelude.Any
  using (Any; any)
open import Prover.Prelude.Decidable
  using (Dec; Decidable; no; yes)
open import Prover.Prelude.Empty
  using (⊥-elim)
open import Prover.Prelude.Equality
  using (_≡_; _≢_; refl; sub; sym; trans)
open import Prover.Prelude.Function
  using (_∘_; id)
open import Prover.Prelude.Inspect
  using ([_]; inspect)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Vec
  using (Vec; []; _∷_)

-- ## Definition

module _Collection
  {A K : Set}
  where

  data Collection
    (f : A → K)
    (p : Decidable K)
    : Set
  
  lookup
    : {f : A → K}
    → {p : Decidable K}
    → Collection f p
    → K
    → Maybe A
  
  data Collection f p where

    empty
      : Collection f p

    insert 
      : (xs : Collection f p)
      → (x : A)
      → .(lookup xs (f x) ≡ nothing {A = A})
      → Collection f p
  
  lookup empty _
    = nothing
  lookup {f = f} {p = p} (insert xs x _) k
    with p k (f x)
  ... | no _
    = lookup xs k
  ... | yes _
    = just x

Collection
  : {A K : Set}
  → (A → K)
  → Decidable K
  → Set
Collection
  = _Collection.Collection

-- ## Module

module Collection where

  open _Collection.Collection public

  open _Collection public
    using (lookup)
  
  -- ### Conversion

  module _
    {A K : Set}
    {f : A → K}
    {p : Decidable K}
    where

    to-vec
      : Collection f p
      → Any (Vec A)
    to-vec empty
      = any []
    to-vec (insert xs x _)
      = any (x ∷ Any.value (to-vec xs))

  -- ### Equality

  module _
    {A K : Set}
    {f : A → K}
    {p : Decidable K}
    where

    decidable
      : Decidable A
      → Decidable (Collection f p)
    
    decidable _ empty empty
      = yes refl
    decidable q (insert xs x _) (insert ys y _)
      with q x y | decidable q xs ys
    ... | yes refl | yes refl
      = yes refl
    ... | no ¬r | _
      = no (λ {refl → ¬r refl})
    ... | _ | no ¬r
      = no (λ {refl → ¬r refl})
    
    decidable q empty (insert _ _ _)
      = no (λ ())
    decidable q (insert _ _ _) empty
      = no (λ ())
  
  -- ### Membership

  module _
    {A K : Set}
    {f : A → K}
    {p : Decidable K}
    where
  
    IsMember
      : (xs : Collection f p)
      → (x : A)
      → Set
    IsMember xs x
      = lookup xs (f x) ≡ just x
    
    is-member?
      : (q : Decidable A)
      → (xs : Collection f p)
      → (x : A)
      → Dec (IsMember xs x)
    is-member? q xs x
      = Maybe.decidable q (lookup xs (f x)) (just x)
    
    record Member
      (xs : Collection f p)
      : Set
      where
    
      constructor
        
        member

      field

        value
          : A

        valid
          : IsMember xs value
    
    lookup-to-eq
      : (xs : Collection f p)
      → (k : K)
      → (x : A)
      → lookup xs k ≡ just x
      → k ≡ f x
    lookup-to-eq empty _ x q
      = ⊥-elim (Maybe.nothing≢just x q)
    lookup-to-eq (insert xs x' _) k x q
      with p k (f x')
    ... | no _ 
      = lookup-to-eq xs k x q
    lookup-to-eq _ _ _ refl | yes r
      = r
    
    lookup-member
      : (xs : Collection f p)
      → K
      → Maybe (Member xs)
    lookup-member xs k
      with lookup xs k
      | inspect (lookup xs) k
    ... | nothing | _
      = nothing
    ... | just x | [ q ]
      = just (member x
        (trans (sub (lookup xs) (sym (lookup-to-eq xs k x q))) q))

  -- ### Properties

  module _
    {A K : Set}
    {f : A → K}
    {p : Decidable K}
    where

    lookup-insert
      : (xs : Collection f p)
      → (x : A)
      → (q : lookup xs (f x) ≡ nothing)
      → lookup (insert xs x q) (f x) ≡ just x
    lookup-insert _ x _
      with p (f x) (f x)
    ... | no ¬r
      = ⊥-elim (¬r refl)
    ... | yes _
      = refl
    
    lookup-other
      : (xs : Collection f p)
      → (x : A)
      → (q : lookup xs (f x) ≡ nothing)
      → (k : K)
      → k ≢ f x
      → lookup (insert xs x q) k ≡ lookup xs k
    lookup-other _ x _ k r
      with p k (f x)
    ... | no _
      = refl
    ... | yes refl
      = ⊥-elim (r refl)
    
    _⊆_
      : (xs₁ xs₂ : Collection f p)
      → Set
    _⊆_ xs₁ xs₂
      = (k : K)
      → (x : A)
      → lookup xs₁ k ≡ just x
      → lookup xs₂ k ≡ just x
    
    ⊆-empty
      : (xs : Collection f p)
      → empty ⊆ xs
    ⊆-empty _ _ _ ()
    
    ⊆-insert
      : (xs₁ xs₂ : Collection f p)
      → (x : A)
      → (q : lookup xs₂ (f x) ≡ nothing)
      → xs₁ ⊆ xs₂
      → xs₁ ⊆ insert xs₂ x q
    ⊆-insert _ xs₂ x q r k y s
      with p k (f x)
    ... | no _
      = r k y s
    ... | yes refl
      with lookup xs₂ k | r (f x) y s
    ... | _ | refl
      = ⊥-elim (Maybe.just≢nothing y q)
    
    ⊆-reflexive
      : (xs : Collection f p)
      → xs ⊆ xs
    ⊆-reflexive _ _ _
      = id
    
    ⊆-transitive
      : (xs₁ xs₂ xs₃ : Collection f p)
      → xs₁ ⊆ xs₂
      → xs₂ ⊆ xs₃
      → xs₁ ⊆ xs₃
    ⊆-transitive _ _ _ p q k x
      = q k x
      ∘ p k x

