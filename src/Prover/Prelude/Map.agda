module Prover.Prelude.Map where

open import Prover.Prelude.Collection
  using (Collection)
open import Prover.Prelude.Decidable
  using (Decidable; no; yes)
open import Prover.Prelude.Empty
  using (⊥-elim)
open import Prover.Prelude.Equality
  using (_≡_; _≢_; refl; sub; sym)
open import Prover.Prelude.Function
  using (_$_; _∘_; id)
open import Prover.Prelude.Inspect
  using ([_]; inspect)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Sigma
  using (module Sigma; _×_; _,_; π₁)

open Collection using ()
  renaming (_⊆_ to Subset)

-- ## Definition

Map
  : {K : Set}
  → Set
  → Decidable K
  → Set
Map {K} V p
  = Collection {K × V} π₁ p

-- ## Module

module Map where

  -- ### Interface

  module _
    {K : Set}
    {p : Decidable K}
    where

    lookup
      : {V : Set}
      → Map V p
      → K
      → Maybe V
    lookup m k
      with Collection.lookup m k
    ... | nothing
      = nothing
    ... | just (_ , v)
      = just v
    
    lookup-to-collection-nothing
      : {V : Set}
      → (m : Map V p)
      → (k : K)
      → lookup m k ≡ nothing
      → Collection.lookup m k ≡ nothing
    lookup-to-collection-nothing m k q
      with Collection.lookup m k
    ... | nothing
      = refl
    ... | just _
      = ⊥-elim (Maybe.just≢nothing q)
    
    empty
      : {V : Set}
      → Map V p
    empty
      = Collection.empty
    
    insert
      : {V : Set}
      → (m : Map V p)
      → (k : K)
      → V
      → lookup m k ≡ nothing
      → Map V p
    insert m k v q
      = Collection.insert m (k , v) (lookup-to-collection-nothing m k q)
  
    map
      : {V W : Set}
      → (V → W)
      → Map V p
      → Map W p
  
    lookup-map-nothing
      : {V W : Set}
      → (f : V → W)
      → (m : Map V p)
      → (k : K)
      → Collection.lookup m k ≡ nothing
      → Collection.lookup (map f m) k ≡ nothing
  
    map _ Collection.empty
      = Collection.empty
    map f (Collection.insert m (k , v) q)
      = Collection.insert (map f m) (k , f v) (lookup-map-nothing f m k q)
  
    lookup-map-nothing _ Collection.empty _ _
      = refl
    lookup-map-nothing f (Collection.insert m (k' , v) _) k q
      with p k k'
    ... | no _
      = lookup-map-nothing f m k q
    ... | yes _
      = ⊥-elim (Maybe.just≢nothing q)

  -- ### Properties

  module _
    {K : Set}
    {p : Decidable K}
    where

    lookup-eq
      : {V : Set}
      → {l : K}
      → {v : V}
      → (m : Map V p)
      → (k : K)
      → Collection.lookup m k ≡ just (l , v)
      → k ≡ l
    lookup-eq m k
      = Collection.lookup-eq m k
    
    lookup-to-collection-just
      : {V : Set}
      → {v : V}
      → (m : Map V p)
      → (k : K)
      → lookup m k ≡ just v
      → Collection.lookup m k ≡ just (k , v)
    lookup-to-collection-just m k q
      with Collection.lookup m k
      | inspect (Collection.lookup m) k
    ... | nothing | _
      = ⊥-elim (Maybe.nothing≢just q)
    ... | just _ | [ r ]
      = sub just (Sigma.comma-eq
        (sym (lookup-eq m k r))
        (Maybe.just-injective q))
    
    lookup-from-collection-just
      : {V : Set}
      → {l : K}
      → {v : V}
      → (m : Map V p)
      → (k : K)
      → Collection.lookup m k ≡ just (l , v)
      → lookup m k ≡ just v
    lookup-from-collection-just m k _
      with Collection.lookup m k
    lookup-from-collection-just _ _ refl | _
      = refl
    
    lookup-from-collection-eq
      : {V : Set}
      → (m : Map V p)
      → (k : K)
      → (m' : Map V p)
      → Collection.lookup m k ≡ Collection.lookup m' k
      → lookup m k ≡ lookup m' k
    lookup-from-collection-eq m k m' _
      with Collection.lookup m k
      | Collection.lookup m' k
    lookup-from-collection-eq _ _ _ refl | _ | nothing
      = refl
    lookup-from-collection-eq _ _ _ refl | _ | just _
      = refl
    
    lookup-insert
      : {V : Set}
      → (m : Map V p)
      → (k : K)
      → (v : V)
      → (eq : lookup m k ≡ nothing)
      → lookup (insert m k v eq) k ≡ just v
    lookup-insert m k v eq
      with Collection.lookup (Collection.insert m (k , v)
        (lookup-to-collection-nothing m k eq)) k
      | Collection.lookup-insert m (k , v)
        (lookup-to-collection-nothing m k eq)
    ... | _ | refl
      = refl
    
    lookup-other
      : {V : Set}
      → (m : Map V p)
      → (l : K)
      → (v : V)
      → (eq : lookup m l ≡ nothing)
      → (k : K)
      → k ≢ l
      → lookup (insert m l v eq) k ≡ lookup m k
    lookup-other m l v q k ¬r
      = lookup-from-collection-eq (insert m l v q) k m
        (Collection.lookup-other m (l , v)
          (lookup-to-collection-nothing m l q) k ¬r)
    
    lookup-map
      : {V W : Set}
      → {v : V}
      → (f : V → W)
      → (m : Map V p)
      → (k : K)
      → lookup m k ≡ just v
      → lookup (map f m) k ≡ just (f v)
    lookup-map _ Collection.empty _ q
      = ⊥-elim (Maybe.nothing≢just q)
    lookup-map _ (Collection.insert m (k' , v') _) k q
      with p k k'
    ... | no _
      with Collection.lookup m k
      | inspect (Collection.lookup m) k
    ... | nothing | _
      = ⊥-elim (Maybe.nothing≢just q)
    lookup-map f (Collection.insert m _ _) k refl
      | no _ | just (k'' , v'') | [ r ]
      with Collection.lookup (map f m) k
      | lookup-to-collection-just (map f m) k
        (lookup-map f m k (lookup-from-collection-just m k r))
    ... | _ | refl
      = refl
    lookup-map _ _ _ refl | yes _
      = refl
    
    _⊆_
      : {V : Set}
      → Map V p
      → Map V p
      → Set
    _⊆_ {V} m₁ m₂
      = {v : V}
      → (k : K)
      → lookup m₁ k ≡ just v
      → lookup m₂ k ≡ just v
    
    ⊆-to-collection
      : {V : Set}
      → (m₁ m₂ : Map V p)
      → m₁ ⊆ m₂
      → Subset m₁ m₂
    ⊆-to-collection m₁ m₂ p k q
      with lookup-eq m₁ k q
    ... | refl
      = lookup-to-collection-just m₂ k
      $ p k
      $ lookup-from-collection-just m₁ k
      $ q
    
    ⊆-from-collection
      : {V : Set}
      → (m₁ m₂ : Map V p)
      → Subset m₁ m₂
      → m₁ ⊆ m₂
    ⊆-from-collection m₁ m₂ p k q
      = lookup-from-collection-just m₂ k
      $ p k
      $ lookup-to-collection-just m₁ k
      $ q
    
    ⊆-empty
      : {V : Set}
      → (m : Map V p)
      → empty ⊆ m
    ⊆-empty _ _ ()
    
    ⊆-insert
      : {V : Set}
      → (m₁ m₂ : Map V p)
      → (k : K)
      → (v : V)
      → (q : lookup m₂ k ≡ nothing)
      → m₁ ⊆ m₂
      → m₁ ⊆ insert m₂ k v q
    ⊆-insert m₁ m₂ k v q
      = ⊆-from-collection m₁ (insert m₂ k v q)
      ∘ Collection.⊆-insert m₁ m₂ (k , v)
        (lookup-to-collection-nothing m₂ k q)
      ∘ ⊆-to-collection m₁ m₂
    
    ⊆-reflexive
      : {V : Set}
      → (m : Map V p)
      → m ⊆ m
    ⊆-reflexive _ _
      = id
    
    ⊆-transitive
      : {V : Set}
      → (m₁ m₂ m₃ : Map V p)
      → m₁ ⊆ m₂
      → m₂ ⊆ m₃
      → m₁ ⊆ m₃
    ⊆-transitive _ _ _ p q k
      = q k
      ∘ p k

