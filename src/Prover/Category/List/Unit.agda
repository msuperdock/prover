module Prover.Category.List.Unit where

open import Prover.Category
  using (module Category'; Category; Functor; FunctorCompose; FunctorEqual;
    FunctorIdentity; FunctorSquare; functor-compose';
    functor-compose-from-equal; functor-identity'; functor-identity-from-equal;
    functor-square-from-equal; functor-sym; functor-trans)
open import Prover.Category.List
  using (module CategoryList; module FunctorList; category-list; functor-list)
open import Prover.Category.Unit
  using (module CategoryUnit; category-unit; functor-unit)
open import Prover.Function
  using (Function; FunctionCompose; FunctionEqual; FunctionIdentity;
    FunctionSquare; function-compose; function-compose-to-equal;
      function-identity; function-identity-to-equal; function-square-to-equal)
open import Prover.Prelude

open List
  using (_∷_; _!_)

-- ## Category

-- ### Function

module CategoryListUnit where

  record Arrow
    {A B : Set}
    (xs : List A)
    (ys : List B)
    : Set
    where

    no-eta-equality

    field

      lookup
        : Fin (List.length xs)
        → Maybe (Fin (List.length ys))

      injective
        : (k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → lookup k₁ ≡ just l
        → lookup k₂ ≡ just l
        → k₁ ≡ k₂

  record ArrowEqual
    {A B : Set}
    {xs : List A}
    {ys : List B}
    (fs₁ fs₂ : Arrow xs ys)
    : Set
    where

    field

      lookup
        : (k : Fin (List.length xs))
        → Arrow.lookup fs₁ k ≡ Arrow.lookup fs₂ k

  abstract

    arrow-refl
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → {fs : Arrow xs ys}
      → ArrowEqual fs fs
    arrow-refl
      = record
      { lookup
        = λ _ → refl
      }

    arrow-sym
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → {fs₁ fs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₁
    arrow-sym ps
      = record
      { lookup
        = λ k → sym
          (ArrowEqual.lookup ps k)
      }

    arrow-trans
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → {fs₁ fs₂ fs₃ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₃
      → ArrowEqual fs₁ fs₃
    arrow-trans ps₁ ps₂
      = record
      { lookup
        = λ k → trans
          (ArrowEqual.lookup ps₁ k)
          (ArrowEqual.lookup ps₂ k)
      }

    simplify-lookup
      : {A B : Set}
      → (xs : List A)
      → (ys : List B)
      → (Fin (List.length xs)
        → Maybe (Fin (List.length ys)))
      → (Fin (List.length xs)
        → Maybe (Fin (List.length ys)))
    simplify-lookup (_ ∷ xs) ys f
      with f zero
      | simplify-lookup xs ys (f ∘ suc)
    ... | v | f'
      = λ
      { zero
        → v
      ; (suc k)
        → f' k
      }

    simplify-lookup-equal
      : {A B : Set}
      → (xs : List A)
      → (ys : List B)
      → (f : Fin (List.length xs)
        → Maybe (Fin (List.length ys)))
      → (k : Fin (List.length xs))
      → simplify-lookup xs ys f k ≡ f k
    simplify-lookup-equal (_ ∷ _) _ _ zero
      = refl
    simplify-lookup-equal (_ ∷ xs) ys f (suc k)
      = simplify-lookup-equal xs ys (f ∘ suc) k

    simplify-injective
      : {A B : Set}
      → (xs : List A)
      → (ys : List B)
      → (f : Fin (List.length xs)
        → Maybe (Fin (List.length ys)))
      → ((k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → f k₁ ≡ just l
        → f k₂ ≡ just l
        → k₁ ≡ k₂)
      → ((k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → simplify-lookup xs ys f k₁ ≡ just l
        → simplify-lookup xs ys f k₂ ≡ just l
        → k₁ ≡ k₂)
    simplify-injective xs ys f p k₁ k₂ q₁ q₂
      = p k₁ k₂
        (trans (sym (simplify-lookup-equal xs ys f k₁)) q₁)
        (trans (sym (simplify-lookup-equal xs ys f k₂)) q₂)

    simplify
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → Arrow xs ys
      → Arrow xs ys
    simplify {xs = xs} {ys = ys} fs
      = record
      { lookup
        = simplify-lookup xs ys
          (Arrow.lookup fs)
      ; injective
        = simplify-injective xs ys
          (Arrow.lookup fs)
          (Arrow.injective fs)
      }

    simplify-equal
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (simplify fs) fs
    simplify-equal {xs = xs} {ys = ys} fs
      = record
      { lookup
        = simplify-lookup-equal xs ys
          (Arrow.lookup fs)
      }

  identity-lookup
    : {A : Set}
    → (xs : List A)
    → Fin (List.length xs)
    → Maybe (Fin (List.length xs))
  identity-lookup _
    = just

  abstract

    identity-injective
      : {A : Set}
      → (xs : List A)
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length xs)}
      → identity-lookup xs k₁ ≡ just l
      → identity-lookup xs k₂ ≡ just l
      → k₁ ≡ k₂
    identity-injective _ _ _ refl refl
      = refl

  identity
    : {A : Set}
    → (xs : List A)
    → Arrow xs xs
  identity xs
    = record
    { lookup
      = identity-lookup xs
    ; injective
      = identity-injective xs
    }

  compose-lookup
    : {A B C : Set}
    → {xs : List A}
    → {ys : List B}
    → {zs : List C}
    → Arrow ys zs
    → Arrow xs ys
    → Fin (List.length xs)
    → Maybe (Fin (List.length zs))
  compose-lookup fs gs k
    with Arrow.lookup gs k
  ... | nothing
    = nothing
  ... | just l
    = Arrow.lookup fs l

  abstract

    compose-injective
      : {A B C : Set}
      → {xs : List A}
      → {ys : List B}
      → {zs : List C}
      → (fs : Arrow ys zs)
      → (gs : Arrow xs ys)
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length zs)}
      → compose-lookup fs gs k₁ ≡ just l
      → compose-lookup fs gs k₂ ≡ just l
      → k₁ ≡ k₂
    compose-injective fs gs k₁ k₂ _ _
      with Arrow.lookup gs k₁
      | inspect (Arrow.lookup gs) k₁
      | Arrow.lookup gs k₂
      | inspect (Arrow.lookup gs) k₂
    ... | just l₁ | _ | just l₂ | _
      with Arrow.lookup fs l₁
      | inspect (Arrow.lookup fs) l₁
      | Arrow.lookup fs l₂
      | inspect (Arrow.lookup fs) l₂
    compose-injective fs gs k₁ k₂ refl refl
      | just l₁ | [ p₁ ] | just l₂ | [ p₂ ]
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      with Arrow.injective fs l₁ l₂ q₁ q₂
    ... | refl
      = Arrow.injective gs k₁ k₂ p₁ p₂

  compose
    : {A B C : Set}
    → {xs : List A}
    → {ys : List B}
    → {zs : List C}
    → Arrow ys zs
    → Arrow xs ys
    → Arrow xs zs
  compose fs gs
    = record
    { lookup
      = compose-lookup fs gs
    ; injective
      = compose-injective fs gs
    }

  abstract

    compose-equal-lookup
      : {A B C : Set}
      → {xs : List A}
      → {ys : List B}
      → {zs : List C}
      → {fs₁ fs₂ : Arrow ys zs}
      → {gs₁ gs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual gs₁ gs₂
      → (k : Fin (List.length xs))
      → Arrow.lookup (compose fs₁ gs₁) k ≡ Arrow.lookup (compose fs₂ gs₂) k
    compose-equal-lookup {gs₁ = gs₁} {gs₂ = gs₂} ps qs k
      with Arrow.lookup gs₁ k
      | Arrow.lookup gs₂ k
      | ArrowEqual.lookup qs k
    ... | nothing | _ | refl
      = refl
    ... | just l | _ | refl
      = ArrowEqual.lookup ps l

    compose-equal
      : {A B C : Set}
      → {xs : List A}
      → {ys : List B}
      → {zs : List C}
      → {fs₁ fs₂ : Arrow ys zs}
      → {gs₁ gs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual gs₁ gs₂
      → ArrowEqual
        (compose fs₁ gs₁)
        (compose fs₂ gs₂)
    compose-equal ps qs
      = record
      { lookup
        = compose-equal-lookup ps qs
      }

    precompose
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (compose fs (identity xs)) fs
    precompose _
      = record
      { lookup
        = λ _ → refl
      }

    postcompose-lookup
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → (fs : Arrow xs ys)
      → (k : Fin (List.length xs))
      → Arrow.lookup (compose (identity ys) fs) k ≡ Arrow.lookup fs k
    postcompose-lookup fs k
      with Arrow.lookup fs k
    ... | nothing
      = refl
    ... | just _
      = refl

    postcompose
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (compose (identity ys) fs) fs
    postcompose fs
      = record
      { lookup
        = postcompose-lookup fs
      }

    associative-lookup
      : {A B C D : Set}
      → {ws : List A}
      → {xs : List B}
      → {ys : List C}
      → {zs : List D}
      → (fs : Arrow ys zs)
      → (gs : Arrow xs ys)
      → (hs : Arrow ws xs)
      → (k : Fin (List.length ws))
      → Arrow.lookup (compose (compose fs gs) hs) k
        ≡ Arrow.lookup (compose fs (compose gs hs)) k
    associative-lookup _ gs hs k
      with Arrow.lookup hs k
    ... | nothing
      = refl
    ... | just l
      with Arrow.lookup gs l
    ... | nothing
      = refl
    ... | just _
      = refl

    associative
      : {A B C D : Set}
      → {ws : List A}
      → {xs : List B}
      → {ys : List C}
      → {zs : List D}
      → (fs : Arrow ys zs)
      → (gs : Arrow xs ys)
      → (hs : Arrow ws xs)
      → ArrowEqual
        (compose (compose fs gs) hs)
        (compose fs (compose gs hs))
    associative fs gs hs
      = record
      { lookup
        = associative-lookup fs gs hs
      }

category-list-unit
  : Set
  → Category
category-list-unit A
  = record
  { CategoryListUnit
  ; Object
    = List A
  }

-- ### Equality

arrow-equal-list-unit
  : {A : Set}
  → {m n : ℕ}
  → {xs₁ xs₂ : Vec A m}
  → {ys₁ ys₂ : Vec A n}
  → {fs₁ : Category.Arrow (category-list-unit A) (any xs₁) (any ys₁)}
  → {fs₂ : Category.Arrow (category-list-unit A) (any xs₂) (any ys₂)}
  → xs₁ ≡ xs₂
  → ys₁ ≡ ys₂
  → ((k : Fin m)
    → CategoryListUnit.Arrow.lookup fs₁ k
    ≡ CategoryListUnit.Arrow.lookup fs₂ k)
  → Category.ArrowEqual' (category-list-unit A) fs₁ fs₂
arrow-equal-list-unit refl refl f
  = Category.any
  $ record
  { lookup
    = f
  }

-- ## Functor

-- ### Function

module _
  {A B : Set}
  where

  module FunctorListUnit
    (F : Function A B)
    where

    base
      : Category.Object (category-list-unit A)
      → Category.Object (category-list-unit B)
    base
      = List.map
        (Function.base F)

    map-lookup
      : {xs ys : Category.Object (category-list-unit A)}
      → Category.Arrow (category-list-unit A) xs ys
      → Fin (List.length (base xs))
      → Maybe (Fin (List.length (base ys)))
    map-lookup
      = CategoryListUnit.Arrow.lookup

    map
      : {xs ys : Category.Object (category-list-unit A)}
      → Category.Arrow (category-list-unit A) xs ys
      → Category.Arrow (category-list-unit B) (base xs) (base ys)
    map fs
      = record
      { lookup
        = map-lookup fs
      ; injective
        = CategoryListUnit.Arrow.injective fs
      }

    abstract

      map-equal
        : {xs ys : Category.Object (category-list-unit A)}
        → {fs₁ fs₂ : Category.Arrow (category-list-unit A) xs ys}
        → Category.ArrowEqual (category-list-unit A) fs₁ fs₂
        → Category.ArrowEqual (category-list-unit B) (map fs₁) (map fs₂)
      map-equal ps
        = record
        { lookup
          = CategoryListUnit.ArrowEqual.lookup ps
        }

      map-identity
        : (xs : Category.Object (category-list-unit A))
        → Category.ArrowEqual (category-list-unit B)
          (map (Category.identity (category-list-unit A) xs))
          (Category.identity (category-list-unit B) (base xs))
      map-identity _
        = record
        { lookup
          = λ _ → refl
        }

      map-compose-lookup
        : {xs ys zs : Category.Object (category-list-unit A)}
        → (fs : Category.Arrow (category-list-unit A) ys zs)
        → (gs : Category.Arrow (category-list-unit A) xs ys)
        → (k : Fin (List.length xs))
        → CategoryListUnit.compose-lookup fs gs k
          ≡ CategoryListUnit.compose-lookup (map fs) (map gs) k
      map-compose-lookup _ gs k
        with CategoryListUnit.Arrow.lookup gs k
      ... | nothing
        = refl
      ... | just _
        = refl

      map-compose
        : {xs ys zs : Category.Object (category-list-unit A)}
        → (fs : Category.Arrow (category-list-unit A) ys zs)
        → (gs : Category.Arrow (category-list-unit A) xs ys)
        → Category.ArrowEqual (category-list-unit B)
          (map (Category.compose (category-list-unit A) fs gs))
          (Category.compose (category-list-unit B) (map fs) (map gs))
      map-compose fs gs
        = record
        { lookup
          = map-compose-lookup fs gs
        }

  functor-list-unit
    : Function A B
    → Functor
      (category-list-unit A)
      (category-list-unit B)
  functor-list-unit F
    = record {FunctorListUnit F}

-- ### Identity

module FunctorListUnitIdentity
  (A : Set)
  where

  base'
    : {n : ℕ}
    → (xs : Vec A n)
    → Vec.map id xs ≡ xs
  base'
    = Vec.map-identity

  base
    : (xs : Category.Object (category-list-unit A))
    → Functor.base
      (functor-list-unit (function-identity A)) xs
    ≅ Functor.base
      (functor-identity' (category-list-unit A)) xs
  base
    = List.map-identity
  
  map
    : {xs ys : Category.Object (category-list-unit A)}
    → (fs : Category.Arrow (category-list-unit A) xs ys)
    → Category'.ArrowEqual'
      (category-list-unit A)
      (category-list-unit A)
      (Functor.map
        (functor-list-unit (function-identity A)) fs)
      (Functor.map
        (functor-identity' (category-list-unit A)) fs)
  map {xs = any xs} {ys = any ys} _
    = arrow-equal-list-unit (base' xs) (base' ys) (λ _ → refl)

functor-list-unit-identity
  : (A : Set)
  → FunctorEqual
    (functor-list-unit (function-identity A))
    (functor-identity' (category-list-unit A))
functor-list-unit-identity A
  = record {FunctorListUnitIdentity A}

-- ### Compose

module _
  {A B C : Set}
  where

  module FunctorListUnitCompose
    (F : Function B C)
    (G : Function A B)
    where

    base'
      : {n : ℕ}
      → (xs : Vec A n)
      → Vec.map (Function.base F ∘ Function.base G) xs
        ≡ Vec.map (Function.base F) (Vec.map (Function.base G) xs)
    base'
      = Vec.map-compose
        (Function.base F)
        (Function.base G)

    base
      : (xs : Category.Object (category-list-unit A))
      → Functor.base
        (functor-list-unit (function-compose F G)) xs
      ≅ Functor.base
        (functor-compose' (functor-list-unit F) (functor-list-unit G)) xs
    base
      = List.map-compose
        (Function.base F)
        (Function.base G)
  
    map
      : {xs ys : Category.Object (category-list-unit A)}
      → (fs : Category.Arrow (category-list-unit A) xs ys)
      → Category'.ArrowEqual'
        (category-list-unit C)
        (category-list-unit C)
        (Functor.map
          (functor-list-unit (function-compose F G)) fs)
        (Functor.map
          (functor-compose' (functor-list-unit F) (functor-list-unit G)) fs)
    map {xs = any xs} {ys = any ys} _
      = arrow-equal-list-unit (base' xs) (base' ys) (λ _ → refl)

  functor-list-unit-compose
    : (F : Function B C)
    → (G : Function A B)
    → FunctorEqual
      (functor-list-unit (function-compose F G))
      (functor-compose' (functor-list-unit F) (functor-list-unit G))
  functor-list-unit-compose F G
    = record {FunctorListUnitCompose F G}

-- ## Functor'

module FunctorListUnit'
  (A : Set)
  where

  base
    : Category.Object (category-list (category-unit A))
    → Category.Object (category-list-unit A)
  base
    = id

  map-lookup
    : {xs ys : Category.Object (category-list (category-unit A))}
    → Category.Arrow (category-list (category-unit A)) xs ys
    → Fin (List.length (base xs))
    → Maybe (Fin (List.length (base ys)))
  map-lookup fs k
    with CategoryList.Arrow.lookup fs k
  ... | nothing
    = nothing
  ... | just (l , _)
    = just l

  abstract
  
    map-injective
      : {xs ys : Category.Object (category-list (category-unit A))}
      → (fs : Category.Arrow (category-list (category-unit A)) xs ys)
      → (k₁ k₂ : Fin (List.length (base xs)))
      → {l : Fin (List.length (base ys))}
      → map-lookup fs k₁ ≡ just l
      → map-lookup fs k₂ ≡ just l
      → k₁ ≡ k₂
    map-injective fs k₁ k₂ _ _
      with CategoryList.Arrow.lookup fs k₁
      | inspect (CategoryList.Arrow.lookup fs) k₁
      | CategoryList.Arrow.lookup fs k₂
      | inspect (CategoryList.Arrow.lookup fs) k₂
    map-injective fs k₁ k₂ refl refl | just _ | [ p₁ ] | just _ | [ p₂ ]
      = CategoryList.Arrow.injective fs k₁ k₂ p₁ p₂

  map
    : {xs ys : Category.Object (category-list (category-unit A))}
    → Category.Arrow (category-list (category-unit A)) xs ys
    → Category.Arrow (category-list-unit A)
      (base xs)
      (base ys)
  map fs
    = record
    { lookup
      = map-lookup fs
    ; injective
      = map-injective fs
    }

  abstract

    map-equal-lookup
      : {xs ys : Category.Object (category-list (category-unit A))}
      → {fs₁ fs₂ : Category.Arrow (category-list (category-unit A)) xs ys}
      → Category.ArrowEqual (category-list (category-unit A)) fs₁ fs₂
      → (k : Fin (List.length xs))
      → map-lookup fs₁ k ≡ map-lookup fs₂ k
    map-equal-lookup {fs₁ = fs₁} {fs₂ = fs₂} ps k
      with CategoryList.Arrow.lookup fs₁ k
      | CategoryList.Arrow.lookup fs₂ k
      | CategoryList.ArrowEqual.lookup ps k
    ... | _ | _ | CategoryList.nothing
      = refl
    ... | _ | _ | CategoryList.just _ _
      = refl

    map-equal
      : {xs ys : Category.Object (category-list (category-unit A))}
      → {fs₁ fs₂ : Category.Arrow (category-list (category-unit A)) xs ys}
      → Category.ArrowEqual (category-list (category-unit A)) fs₁ fs₂
      → Category.ArrowEqual (category-list-unit A)
        (map fs₁)
        (map fs₂)
    map-equal ps
      = record
      { lookup
        = map-equal-lookup ps
      }

    map-identity
      : (xs : Category.Object (category-list (category-unit A)))
      → Category.ArrowEqual (category-list-unit A)
        (map (Category.identity (category-list (category-unit A)) xs))
        (Category.identity (category-list-unit A) (base xs))
    map-identity _
      = record
      { lookup
        = λ _ → refl
      }

    map-compose-lookup
      : {xs ys zs : Category.Object (category-list (category-unit A))}
      → (fs : Category.Arrow (category-list (category-unit A)) ys zs)
      → (gs : Category.Arrow (category-list (category-unit A)) xs ys)
      → (k : Fin (List.length xs))
      → map-lookup (Category.compose (category-list (category-unit A)) fs gs) k
        ≡ CategoryListUnit.compose-lookup (map fs) (map gs) k
    map-compose-lookup fs gs k
      with CategoryList.Arrow.lookup gs k
    ... | nothing
      = refl
    ... | just (l , _)
      with CategoryList.Arrow.lookup fs l
    ... | nothing
      = refl
    ... | just _
      = refl

    map-compose
      : {xs ys zs : Category.Object (category-list (category-unit A))}
      → (fs : Category.Arrow (category-list (category-unit A)) ys zs)
      → (gs : Category.Arrow (category-list (category-unit A)) xs ys)
      → Category.ArrowEqual (category-list-unit A)
        (map (Category.compose (category-list (category-unit A)) fs gs))
        (Category.compose (category-list-unit A) (map fs) (map gs))
    map-compose fs gs
      = record
      { lookup
        = map-compose-lookup fs gs
      }

functor-list-unit'
  : (A : Set)
  → Functor
    (category-list (category-unit A))
    (category-list-unit A)
functor-list-unit' A
  = record {FunctorListUnit' A}

-- ## Functor''

module FunctorListUnit''
  (A : Set)
  where

  base
    : Category.Object (category-list-unit A)
    → Category.Object (category-list (category-unit A))
  base
    = id

  map-lookup
    : {xs ys : Category.Object (category-list-unit A)}
    → Category.Arrow (category-list-unit A) xs ys
    → (k : Fin (List.length (base xs)))
    → Maybe (l ∈ Fin (List.length (base ys))
      × Category.Arrow (category-unit A) (base xs ! k) (base ys ! l))
  map-lookup fs k
    with CategoryListUnit.Arrow.lookup fs k
  ... | nothing
    = nothing
  ... | just l
    = just (l , CategoryUnit.arrow)

  abstract

    map-injective
      : {xs ys : Category.Object (category-list-unit A)}
      → (fs : Category.Arrow (category-list-unit A) xs ys)
      → (k₁ k₂ : Fin (List.length (base xs)))
      → {l : Fin (List.length (base ys))}
      → {f₁ : Category.Arrow (category-unit A) (base xs ! k₁) (base ys ! l)}
      → {f₂ : Category.Arrow (category-unit A) (base xs ! k₂) (base ys ! l)}
      → map-lookup fs k₁ ≡ just (l , f₁)
      → map-lookup fs k₂ ≡ just (l , f₂)
      → k₁ ≡ k₂
    map-injective fs k₁ k₂ _ _
      with CategoryListUnit.Arrow.lookup fs k₁
      | inspect (CategoryListUnit.Arrow.lookup fs) k₁
      | CategoryListUnit.Arrow.lookup fs k₂
      | inspect (CategoryListUnit.Arrow.lookup fs) k₂
    map-injective fs k₁ k₂ refl refl | just _ | [ p₁ ] | just _ | [ p₂ ]
      = CategoryListUnit.Arrow.injective fs k₁ k₂ p₁ p₂

  map
    : {xs ys : Category.Object (category-list-unit A)}
    → Category.Arrow (category-list-unit A) xs ys
    → Category.Arrow (category-list (category-unit A))
      (base xs)
      (base ys)
  map fs
    = record
    { lookup
      = map-lookup fs
    ; injective
      = map-injective fs
    }

  abstract

    map-equal-lookup
      : {xs ys : Category.Object (category-list-unit A)}
      → {fs₁ fs₂ : Category.Arrow (category-list-unit A) xs ys}
      → Category.ArrowEqual (category-list-unit A) fs₁ fs₂
      → (k : Fin (List.length xs))
      → CategoryList.LookupEqual (category-unit A) (base xs) (base ys) k
        (map-lookup fs₁ k)
        (map-lookup fs₂ k)
    map-equal-lookup {fs₁ = fs₁} {fs₂ = fs₂} ps k
      with CategoryListUnit.Arrow.lookup fs₁ k
      | CategoryListUnit.Arrow.lookup fs₂ k
      | CategoryListUnit.ArrowEqual.lookup ps k
    ... | nothing | _ | refl
      = CategoryList.nothing
    ... | just l | _ | refl
      = CategoryList.just l refl

    map-equal
      : {xs ys : Category.Object (category-list-unit A)}
      → {fs₁ fs₂ : Category.Arrow (category-list-unit A) xs ys}
      → Category.ArrowEqual (category-list-unit A) fs₁ fs₂
      → Category.ArrowEqual (category-list (category-unit A))
        (map fs₁)
        (map fs₂)
    map-equal ps
      = record
      { lookup
        = map-equal-lookup ps
      }

    map-identity
      : (xs : Category.Object (category-list-unit A))
      → Category.ArrowEqual (category-list (category-unit A))
        (map (Category.identity (category-list-unit A) xs))
        (Category.identity (category-list (category-unit A)) (base xs))
    map-identity _
      = record
      { lookup
        = λ k → CategoryList.just k refl
      }

    map-compose-lookup
      : {xs ys zs : Category.Object (category-list-unit A)}
      → (fs : Category.Arrow (category-list-unit A) ys zs)
      → (gs : Category.Arrow (category-list-unit A) xs ys)
      → (k : Fin (List.length xs))
      → CategoryList.LookupEqual (category-unit A) (base xs) (base zs) k
        (map-lookup (Category.compose (category-list-unit A) fs gs) k)
        (CategoryList.compose-lookup (category-unit A) (map fs) (map gs) k)
    map-compose-lookup fs gs k
      with CategoryListUnit.Arrow.lookup gs k
    ... | nothing
      = CategoryList.nothing
    ... | just l
      with CategoryListUnit.Arrow.lookup fs l
    ... | nothing
      = CategoryList.nothing
    ... | just m
      = CategoryList.just m refl

    map-compose
      : {xs ys zs : Category.Object (category-list-unit A)}
      → (fs : Category.Arrow (category-list-unit A) ys zs)
      → (gs : Category.Arrow (category-list-unit A) xs ys)
      → Category.ArrowEqual (category-list (category-unit A))
        (map (Category.compose (category-list-unit A) fs gs))
        (Category.compose (category-list (category-unit A)) (map fs) (map gs))
    map-compose fs gs
      = record
      { lookup
        = map-compose-lookup fs gs
      }

functor-list-unit''
  : (A : Set)
  → Functor
    (category-list-unit A)
    (category-list (category-unit A))
functor-list-unit'' A
  = record {FunctorListUnit'' A}

-- ## FunctorEqual

module _
  {A B : Set}
  {F₁ F₂ : Function A B}
  where

  module FunctorEqualListUnit
    (p : FunctionEqual F₁ F₂)
    where

    base'
      : {n : ℕ}
      → (xs : Vec A n)
      → Vec.map (Function.base F₁) xs
        ≡ Vec.map (Function.base F₂) xs
    base'
      = Vec.map-equal
        (Function.base F₁)
        (Function.base F₂)
        (FunctionEqual.base p)

    base
      : (xs : Category.Object (category-list-unit A))
      → Functor.base (functor-list-unit F₁) xs
        ≅ Functor.base (functor-list-unit F₂) xs
    base
      = List.map-equal
        (Function.base F₁)
        (Function.base F₂)
        (FunctionEqual.base p)
  
    map
      : {xs ys : Category.Object (category-list-unit A)}
      → (fs : Category.Arrow (category-list-unit A) xs ys)
      → Category'.ArrowEqual'
        (category-list-unit B)
        (category-list-unit B)
        (Functor.map (functor-list-unit F₁) fs)
        (Functor.map (functor-list-unit F₂) fs)
    map {xs = any xs} {ys = any ys} _
      = arrow-equal-list-unit (base' xs) (base' ys) (λ _ → refl)

  functor-equal-list-unit
    : FunctionEqual F₁ F₂
    → FunctorEqual
      (functor-list-unit F₁)
      (functor-list-unit F₂)
  functor-equal-list-unit p
    = record {FunctorEqualListUnit p}

-- ## FunctorIdentity

functor-identity-list-unit
  : {A : Set}
  → {F : Function A A}
  → FunctionIdentity F
  → FunctorIdentity
    (functor-list-unit F)
functor-identity-list-unit {A  = A} p
  = functor-identity-from-equal
  $ functor-trans (functor-equal-list-unit
    (function-identity-to-equal p))
  $ functor-list-unit-identity A

-- ## FunctorCompose

functor-compose-list-unit
  : {A B C : Set}
  → {F : Function B C}
  → {G : Function A B}
  → {H : Function A C}
  → FunctionCompose F G H
  → FunctorCompose
    (functor-list-unit F)
    (functor-list-unit G)
    (functor-list-unit H)
functor-compose-list-unit {F = F} {G = G} p
  = functor-compose-from-equal
    (functor-list-unit F)
    (functor-list-unit G)
  $ functor-trans (functor-equal-list-unit
    (function-compose-to-equal p))
  $ functor-list-unit-compose F G

-- ## FunctorSquare

functor-square-list-unit
  : {A₁ A₂ B₁ B₂ : Set}
  → {F : Function A₁ A₂}
  → {G : Function B₁ B₂}
  → {H₁ : Function A₁ B₁}
  → {H₂ : Function A₂ B₂}
  → FunctionSquare F G H₁ H₂
  → FunctorSquare
    (functor-list-unit F)
    (functor-list-unit G)
    (functor-list-unit H₁)
    (functor-list-unit H₂)
functor-square-list-unit {F = F} {G = G} {H₁ = H₁} {H₂ = H₂} s
  = functor-square-from-equal
    (functor-list-unit F)
    (functor-list-unit G)
    (functor-list-unit H₁)
    (functor-list-unit H₂)
  $ functor-trans (functor-sym
    (functor-list-unit-compose H₂ F))
  $ functor-trans (functor-equal-list-unit
    (function-square-to-equal s))
  $ functor-list-unit-compose G H₁

-- ## FunctorSquare'

module _
  {A₁ A₂ : Set}
  where

  module FunctorSquareListUnit'
    (F : Function A₁ A₂)
    where

    base
      : (xs₁ : Category.Object (category-list (category-unit A₁)))
      → Functor.base (functor-list-unit' A₂)
        (Functor.base (functor-list (functor-unit F)) xs₁) 
      ≅ Functor.base (functor-list-unit F)
        (Functor.base (functor-list-unit' A₁) xs₁)
    base _
      = refl

    map'
      : {xs₁ ys₁ : Category.Object (category-list (category-unit A₁))}
      → (fs₁ : Category.Arrow (category-list (category-unit A₁)) xs₁ ys₁)
      → (k : Fin (List.length xs₁))
      → FunctorListUnit'.map-lookup A₂
        (Functor.map (functor-list (functor-unit F)) fs₁) k
      ≡ FunctorListUnit.map-lookup F
        (Functor.map (functor-list-unit' A₁) fs₁) k
    map' fs₁ k
      with CategoryList.Arrow.lookup fs₁ k
    ... | nothing
      = refl
    ... | just _
      = refl

    map
      : {xs₁ ys₁ : Category.Object (category-list (category-unit A₁))}
      → (fs₁ : Category.Arrow (category-list (category-unit A₁)) xs₁ ys₁)
      → Category'.ArrowEqual'
        (category-list-unit A₂)
        (category-list-unit A₂)
        (Functor.map (functor-list-unit' A₂)
          (Functor.map (functor-list (functor-unit F)) fs₁))
        (Functor.map (functor-list-unit F)
          (Functor.map (functor-list-unit' A₁) fs₁))
    map fs₁
      = Category.any
      $ record
      { lookup
        = map' fs₁
      }

  functor-square-list-unit'
    : (F : Function A₁ A₂)
    → FunctorSquare
      (functor-list (functor-unit F))
      (functor-list-unit F)
      (functor-list-unit' A₁)
      (functor-list-unit' A₂)
  functor-square-list-unit' F
    = record {FunctorSquareListUnit' F}

-- ## FunctorSquare''

module _
  {A₁ A₂ : Set}
  where

  module FunctorSquareListUnit''
    (F : Function A₁ A₂)
    where

    base
      : (xs₁ : Category.Object (category-list-unit A₁))
      → Functor.base (functor-list-unit'' A₂)
        (Functor.base (functor-list-unit F) xs₁) 
      ≅ Functor.base (functor-list (functor-unit F))
        (Functor.base (functor-list-unit'' A₁) xs₁)
    base _
      = refl

    map'
      : {xs₁ ys₁ : Category.Object (category-list-unit A₁)}
      → (fs₁ : Category.Arrow (category-list-unit A₁) xs₁ ys₁)
      → (k : Fin (List.length xs₁))
      → CategoryList.LookupEqual
        (category-unit A₂)
        (Functor.base (functor-list-unit'' A₂)
          (Functor.base (functor-list-unit F) xs₁))
        (Functor.base (functor-list-unit'' A₂)
          (Functor.base (functor-list-unit F) ys₁)) k
        (FunctorListUnit''.map-lookup A₂
          (Functor.map (functor-list-unit F) fs₁) k)
        (FunctorList.map-lookup (functor-unit F)
          (Functor.map (functor-list-unit'' A₁) fs₁) k)
    map' fs₁ k
      with CategoryListUnit.Arrow.lookup fs₁ k
    ... | nothing
      = CategoryList.nothing
    ... | just l
      = CategoryList.just l refl

    map
      : {xs₁ ys₁ : Category.Object (category-list-unit A₁)}
      → (fs₁ : Category.Arrow (category-list-unit A₁) xs₁ ys₁)
      → Category'.ArrowEqual'
        (category-list (category-unit A₂))
        (category-list (category-unit A₂))
        (Functor.map (functor-list-unit'' A₂)
          (Functor.map (functor-list-unit F) fs₁))
        (Functor.map (functor-list (functor-unit F))
          (Functor.map (functor-list-unit'' A₁) fs₁))
    map fs₁
      = Category.any
      $ record
      { lookup
        = map' fs₁
      }

  functor-square-list-unit''
    : (F : Function A₁ A₂)
    → FunctorSquare
      (functor-list-unit F)
      (functor-list (functor-unit F))
      (functor-list-unit'' A₁)
      (functor-list-unit'' A₂)
  functor-square-list-unit'' F
    = record {FunctorSquareListUnit'' F}

