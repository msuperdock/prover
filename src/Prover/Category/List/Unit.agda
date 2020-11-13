module Prover.Category.List.Unit where

open import Prover.Category
  using (Category)
open import Prover.Prelude

open List
  using (_∷_)

-- ## Category

module CategoryListUnit where

  record Arrow
    {A B : Set}
    (xs : List A)
    (ys : List B)
    : Set
    where

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

    precompose-lookup
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → (fs : Arrow xs ys)
      → (k : Fin (List.length xs))
      → Arrow.lookup (compose fs (identity xs)) k ≡ Arrow.lookup fs k
    precompose-lookup _ _
      = refl

    precompose
      : {A B : Set}
      → {xs : List A}
      → {ys : List B}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (compose fs (identity xs)) fs
    precompose fs
      = record
      { lookup
        = precompose-lookup fs
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

