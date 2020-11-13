module Prover.Category.List where

open import Prover.Category
  using (module Category'; Category; Functor; FunctorCompose; FunctorEqual;
    FunctorIdentity; FunctorSquare; functor-compose';
    functor-compose-from-equal; functor-compose-to-equal; functor-identity';
    functor-identity-from-equal; functor-identity-to-equal;
    functor-square-from-equal; functor-square-to-equal; functor-sym;
    functor-trans)
open import Prover.Prelude

open List
  using (_∷_; _!_)

-- ## Category

-- ### Function

module CategoryList
  (C : Category)
  where

  Object
    : Set
  Object
    = List
      (Category.Object C)

  record Arrow
    (xs ys : Object)
    : Set
    where

    field

      lookup
        : (k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Category.Arrow C (xs ! k) (ys ! l))

      injective
        : (k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → {f₁ : Category.Arrow C (xs ! k₁) (ys ! l)}
        → {f₂ : Category.Arrow C (xs ! k₂) (ys ! l)}
        → lookup k₁ ≡ just (l , f₁)
        → lookup k₂ ≡ just (l , f₂)
        → k₁ ≡ k₂

  data LookupEqual
    (xs ys : Object)
    (k : Fin (List.length xs))
    : Maybe (l ∈ Fin (List.length ys)
      × Category.Arrow C (xs ! k) (ys ! l))
    → Maybe (l ∈ Fin (List.length ys)
      × Category.Arrow C (xs ! k) (ys ! l))
    → Set
    where

    nothing
      : LookupEqual xs ys k nothing nothing

    just
      : (l : Fin (List.length ys))
      → {f₁ f₂ : Category.Arrow C (xs ! k) (ys ! l)}
      → Category.ArrowEqual C f₁ f₂
      → LookupEqual xs ys k (just (l , f₁)) (just (l , f₂))

  lookup-refl
    : {xs ys : Object}
    → {k : Fin (List.length xs)}
    → {f : Maybe (l ∈ Fin (List.length ys)
      × Category.Arrow C (xs ! k) (ys ! l))}
    → LookupEqual xs ys k f f
  lookup-refl {f = nothing}
    = nothing
  lookup-refl {f = just (l , _)}
    = just l (Category.arrow-refl C)

  lookup-refl'
    : {xs ys : Object}
    → {k : Fin (List.length xs)}
    → {f₁ f₂ : Maybe (l ∈ Fin (List.length ys)
      × Category.Arrow C (xs ! k) (ys ! l))}
    → f₁ ≡ f₂
    → LookupEqual xs ys k f₁ f₂
  lookup-refl' refl
    = lookup-refl

  lookup-sym
    : {xs ys : Object}
    → {k : Fin (List.length xs)}
    → {f₁ f₂ : Maybe (l ∈ Fin (List.length ys)
      × Category.Arrow C (xs ! k) (ys ! l))}
    → LookupEqual xs ys k f₁ f₂
    → LookupEqual xs ys k f₂ f₁
  lookup-sym nothing
    = nothing
  lookup-sym (just l p)
    = just l (Category.arrow-sym C p)

  lookup-trans
    : {xs ys : Object}
    → {k : Fin (List.length xs)}
    → {f₁ f₂ f₃ : Maybe (l ∈ Fin (List.length ys)
      × Category.Arrow C (xs ! k) (ys ! l))}
    → LookupEqual xs ys k f₁ f₂
    → LookupEqual xs ys k f₂ f₃
    → LookupEqual xs ys k f₁ f₃
  lookup-trans nothing nothing
    = nothing
  lookup-trans (just l p₁) (just _ p₂)
    = just l (Category.arrow-trans C p₁ p₂)

  data LookupEqual'
    {m n : ℕ}
    (xs₁ xs₂ : Vec (Category.Object C) m)
    (ys₁ ys₂ : Vec (Category.Object C) n)
    (k : Fin m)
    : Maybe (l ∈ Fin n
      × Category.Arrow C (Vec.lookup xs₁ k) (Vec.lookup ys₁ l))
    → Maybe (l ∈ Fin n
      × Category.Arrow C (Vec.lookup xs₂ k) (Vec.lookup ys₂ l))
    → Set
    where

    nothing'
      : LookupEqual' xs₁ xs₂ ys₁ ys₂ k nothing nothing

    just'
      : (l : Fin n)
      → {f₁ : Category.Arrow C (Vec.lookup xs₁ k) (Vec.lookup ys₁ l)}
      → {f₂ : Category.Arrow C (Vec.lookup xs₂ k) (Vec.lookup ys₂ l)}
      → Category.ArrowEqual' C f₁ f₂
      → LookupEqual' xs₁ xs₂ ys₁ ys₂ k (just (l , f₁)) (just (l , f₂))

  lookup-equal'
    : {m n : ℕ}
    → {xs : Vec (Category.Object C) m}
    → {ys : Vec (Category.Object C) n}
    → {k : Fin m}
    → {f₁ f₂ : Maybe (l ∈ Fin n
        × Category.Arrow C (Vec.lookup xs k) (Vec.lookup ys l))}
    → LookupEqual' xs xs ys ys k f₁ f₂
    → LookupEqual (any xs) (any ys) k f₁ f₂
  lookup-equal' nothing'
    = nothing
  lookup-equal' (just' l p)
    = just l (Category.any' C p)

  record ArrowEqual
    {xs ys : Object}
    (fs₁ fs₂ : Arrow xs ys)
    : Set
    where

    field

      lookup
        : (k : Fin (List.length xs))
        → LookupEqual xs ys k
          (Arrow.lookup fs₁ k)
          (Arrow.lookup fs₂ k)

  abstract

    arrow-refl
      : {xs ys : Object}
      → {fs : Arrow xs ys}
      → ArrowEqual fs fs
    arrow-refl
      = record
      { lookup
        = λ _ → lookup-refl
      }

    arrow-sym
      : {xs ys : Object}
      → {fs₁ fs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₁
    arrow-sym ps
      = record
      { lookup
        = λ k → lookup-sym
          (ArrowEqual.lookup ps k)
      }

    arrow-trans
      : {xs ys : Object}
      → {fs₁ fs₂ fs₃ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₃
      → ArrowEqual fs₁ fs₃
    arrow-trans ps₁ ps₂
      = record
      { lookup
        = λ k → lookup-trans
          (ArrowEqual.lookup ps₁ k)
          (ArrowEqual.lookup ps₂ k)
      }

    simplify-lookup
      : (xs ys : Object)
      → ((k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Category.Arrow C (xs ! k) (ys ! l)))
      → ((k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Category.Arrow C (xs ! k) (ys ! l)))
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
      : (xs ys : Object)
      → (f : (k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Category.Arrow C (xs ! k) (ys ! l)))
      → (k : Fin (List.length xs))
      → simplify-lookup xs ys f k ≡ f k
    simplify-lookup-equal (_ ∷ _) _ _ zero
      = refl
    simplify-lookup-equal (_ ∷ xs) ys f (suc k)
      = simplify-lookup-equal xs ys (f ∘ suc) k

    simplify-injective
      : (xs ys : Object)
      → (f : (k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Category.Arrow C (xs ! k) (ys ! l)))
      → ((k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → {g₁ : Category.Arrow C (xs ! k₁) (ys ! l)}
        → {g₂ : Category.Arrow C (xs ! k₂) (ys ! l)}
        → f k₁ ≡ just (l , g₁)
        → f k₂ ≡ just (l , g₂)
        → k₁ ≡ k₂)
      → ((k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → {g₁ : Category.Arrow C (xs ! k₁) (ys ! l)}
        → {g₂ : Category.Arrow C (xs ! k₂) (ys ! l)}
        → simplify-lookup xs ys f k₁ ≡ just (l , g₁)
        → simplify-lookup xs ys f k₂ ≡ just (l , g₂)
        → k₁ ≡ k₂)
    simplify-injective xs ys f p k₁ k₂ q₁ q₂
      = p k₁ k₂
        (trans (sym (simplify-lookup-equal xs ys f k₁)) q₁)
        (trans (sym (simplify-lookup-equal xs ys f k₂)) q₂)

    simplify
      : {xs ys : Object}
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
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (simplify fs) fs
    simplify-equal {xs = xs} {ys = ys} fs
      = record
      { lookup
        = λ k
        → lookup-refl'
        $ simplify-lookup-equal xs ys
          (Arrow.lookup fs) k
      }

  identity-lookup
    : (xs : Object)
    → (k : Fin (List.length xs))
    → Maybe (l ∈ Fin (List.length xs)
      × Category.Arrow C (xs ! k) (xs ! l))
  identity-lookup xs k
    = just (k , Category.identity C (xs ! k))

  abstract

    identity-injective
      : (xs : Object)
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length xs)}
      → {f₁ : Category.Arrow C (xs ! k₁) (xs ! l)}
      → {f₂ : Category.Arrow C (xs ! k₂) (xs ! l)}
      → identity-lookup xs k₁ ≡ just (l , f₁)
      → identity-lookup xs k₂ ≡ just (l , f₂)
      → k₁ ≡ k₂
    identity-injective _ _ _ refl refl
      = refl

  identity
    : (xs : Object)
    → Arrow xs xs
  identity xs
    = record
    { lookup
      = identity-lookup xs
    ; injective
      = identity-injective xs
    }

  compose-lookup
    : {xs ys zs : Object}
    → Arrow ys zs
    → Arrow xs ys
    → (k : Fin (List.length xs))
    → Maybe (l ∈ Fin (List.length zs)
      × Category.Arrow C (xs ! k) (zs ! l))
  compose-lookup fs gs k
    with Arrow.lookup gs k
  ... | nothing
    = nothing
  ... | just (l , g)
    with Arrow.lookup fs l
  ... | nothing
    = nothing
  ... | just (m , f)
    = just (m , Category.compose C f g)

  abstract

    compose-injective
      : {xs ys zs : Object}
      → (fs : Arrow ys zs)
      → (gs : Arrow xs ys)
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length zs)}
      → {f₁ : Category.Arrow C (xs ! k₁) (zs ! l)}
      → {f₂ : Category.Arrow C (xs ! k₂) (zs ! l)}
      → compose-lookup fs gs k₁ ≡ just (l , f₁)
      → compose-lookup fs gs k₂ ≡ just (l , f₂)
      → k₁ ≡ k₂
    compose-injective fs gs k₁ k₂ _ _
      with Arrow.lookup gs k₁
      | inspect (Arrow.lookup gs) k₁
      | Arrow.lookup gs k₂
      | inspect (Arrow.lookup gs) k₂
    ... | just (l₁ , _) | _ | just (l₂ , _) | _
      with Arrow.lookup fs l₁
      | inspect (Arrow.lookup fs) l₁
      | Arrow.lookup fs l₂
      | inspect (Arrow.lookup fs) l₂
    compose-injective fs gs k₁ k₂ refl refl
      | just (l₁ , _) | [ p₁ ] | just (l₂ , _) | [ p₂ ]
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      with Arrow.injective fs l₁ l₂ q₁ q₂
    ... | refl
      = Arrow.injective gs k₁ k₂ p₁ p₂

  compose
    : {xs ys zs : Object}
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
      : {xs ys zs : Object}
      → {fs₁ fs₂ : Arrow ys zs}
      → {gs₁ gs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual gs₁ gs₂
      → (k : Fin (List.length xs))
      → LookupEqual xs zs k
        (Arrow.lookup (compose fs₁ gs₁) k)
        (Arrow.lookup (compose fs₂ gs₂) k)
    compose-equal-lookup {fs₁ = fs₁} {fs₂ = fs₂} {gs₁ = gs₁} {gs₂ = gs₂} ps qs k
      with Arrow.lookup gs₁ k
      | Arrow.lookup gs₂ k
      | ArrowEqual.lookup qs k
    ... | _ | _ | nothing
      = nothing
    ... | _ | _ | just l q'
      with Arrow.lookup fs₁ l
      | Arrow.lookup fs₂ l
      | ArrowEqual.lookup ps l
    ... | _ | _ | nothing
      = nothing
    ... | _ | _ | just m p'
      = just m (Category.compose-equal C p' q')

    compose-equal
      : {xs ys zs : Object}
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
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → (k : Fin (List.length xs))
      → LookupEqual xs ys k
        (Arrow.lookup (compose fs (identity xs)) k)
        (Arrow.lookup fs k)
    precompose-lookup fs k
      with Arrow.lookup fs k
    ... | nothing
      = nothing
    ... | just (l , f)
      = just l (Category.precompose C f)

    precompose
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (compose fs (identity xs)) fs
    precompose fs
      = record
      { lookup
        = precompose-lookup fs
      }

    postcompose-lookup
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → (k : Fin (List.length xs))
      → LookupEqual xs ys k
        (Arrow.lookup (compose (identity ys) fs) k)
        (Arrow.lookup fs k)
    postcompose-lookup fs k
      with Arrow.lookup fs k
    ... | nothing
      = nothing
    ... | just (l , f)
      = just l (Category.postcompose C f)

    postcompose
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (compose (identity ys) fs) fs
    postcompose fs
      = record
      { lookup
        = postcompose-lookup fs
      }

    associative-lookup
      : {ws xs ys zs : Object}
      → (fs : Arrow ys zs)
      → (gs : Arrow xs ys)
      → (hs : Arrow ws xs)
      → (k : Fin (List.length ws))
      → LookupEqual ws zs k
        (Arrow.lookup (compose (compose fs gs) hs) k)
        (Arrow.lookup (compose fs (compose gs hs)) k)
    associative-lookup fs gs hs k
      with Arrow.lookup hs k
    ... | nothing
      = nothing
    ... | just (l , h)
      with Arrow.lookup gs l
    ... | nothing
      = nothing
    ... | just (m , g)
      with Arrow.lookup fs m
    ... | nothing
      = nothing
    ... | just (n , f)
      = just n (Category.associative C f g h)

    associative
      : {ws xs ys zs : Object}
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

  update-lookup
    : {y : Category.Object C}
    → (xs : Object)
    → (k : Fin (List.length xs))
    → Category.Arrow C (xs ! k) y
    → (k' : Fin (List.length xs))
    → Category.Arrow C (xs ! k') (List.update xs k y ! k')
  update-lookup {y = y} xs k f k'
    with k ≟ k' fin
  ... | no ¬p
    = rewrite'
      (Category.Arrow C (xs ! k'))
      (List.lookup-update-other xs k k' y ¬p)
      (Category.identity C (xs ! k'))
  ... | yes refl
    = rewrite'
      (Category.Arrow C (xs ! k'))
      (List.lookup-update xs k y) f

  update
    : {y : Category.Object C}
    → (xs : Object)
    → (k : Fin (List.length xs))
    → Category.Arrow C (xs ! k) y
    → Arrow xs (List.update xs k y)
  update xs k f
    = record
    { lookup
      = λ l → just (l , update-lookup xs k f l)
    ; injective
      = λ {_ _ refl refl → refl}
    }

  insert-lookup
    : (xs : Object)
    → (k : Fin (suc (List.length xs)))
    → (y : Category.Object C)
    → (k' : Fin (List.length xs))
    → l ∈ Fin (suc (List.length xs))
    × Category.Arrow C (xs ! k') (List.insert xs k y ! l)
  insert-lookup xs k y k'
    with Fin.compare (Fin.lift k') k
  ... | τ₁ p _ _
    = Fin.lift k'
    , rewrite'
      (Category.Arrow C (xs ! k'))
      (List.lookup-insert-less xs y k' p)
      (Category.identity C (xs ! k'))
  ... | τ₂ ¬p _ _
    = suc k'
    , rewrite'
      (Category.Arrow C (xs ! k'))
      (List.lookup-insert-¬less xs k y k' ¬p)
      (Category.identity C (xs ! k'))
  ... | τ₃ ¬p _ _
    = suc k'
    , rewrite'
      (Category.Arrow C (xs ! k'))
      (List.lookup-insert-¬less xs k y k' ¬p)
      (Category.identity C (xs ! k'))

  insert-injective
    : (xs : Object)
    → (k : Fin (suc (List.length xs)))
    → (y : Category.Object C)
    → (k₁' k₂' : Fin (List.length xs))
    → {l : Fin (suc (List.length xs))}
    → {f₁ : Category.Arrow C (xs ! k₁') (List.insert xs k y ! l)}
    → {f₂ : Category.Arrow C (xs ! k₂') (List.insert xs k y ! l)}
    → insert-lookup xs k y k₁' ≡ (l , f₁)
    → insert-lookup xs k y k₂' ≡ (l , f₂)
    → k₁' ≡ k₂'
  insert-injective _ k _ k₁' k₂' p₁ p₂
    with Fin.compare (Fin.lift k₁') k
    | Fin.compare (Fin.lift k₂') k
    | Sigma.comma-injective₁ p₁
    | Sigma.comma-injective₁ p₂

  ... | τ₁ _ _ _ | τ₁ _ _ _ | q₁ | q₂
    = Fin.lift-injective k₁' k₂' (trans q₁ (sym q₂))
  ... | τ₂ _ _ _ | τ₂ _ _ _ | refl | refl
    = refl
  ... | τ₂ _ _ _ | τ₃ _ _ _ | refl | refl
    = refl
  ... | τ₃ _ _ _ | τ₃ _ _ _ | refl | refl
    = refl
  ... | τ₃ _ _ _ | τ₂ _ _ _ | refl | refl
    = refl

  ... | τ₁ r₁ _ _ | τ₂ _ refl _ | refl | q₂
    = ⊥-elim (Fin.<-¬refl' (sym q₂)
      (Fin.<-trans r₁ (Fin.<-suc k₂')))
  ... | τ₁ r₁ _ _ | τ₃ _ _ r₂ | refl | q₂
    = ⊥-elim (Fin.<-¬refl' (sym q₂)
      (Fin.<-trans r₁ (Fin.<-trans r₂ (Fin.<-suc k₂'))))
  ... | τ₂ _ refl _ | τ₁ r₁ _ _ | q₁ | refl
    = ⊥-elim (Fin.<-¬refl' (sym q₁)
      (Fin.<-trans r₁ (Fin.<-suc k₁')))
  ... | τ₃ _ _ r₁ | τ₁ r₂ _ _ | q₁ | refl
    = ⊥-elim (Fin.<-¬refl' (sym q₁)
      (Fin.<-trans r₂ (Fin.<-trans r₁ (Fin.<-suc k₁'))))

  insert
    : (xs : Object)
    → (k : Fin (suc (List.length xs)))
    → (y : Category.Object C)
    → Arrow xs (List.insert xs k y)
  insert xs k y
    = record
    { lookup
      = λ k'
      → just
        (insert-lookup xs k y k')
    ; injective
      = λ k₁' k₂' p₁ p₂
      → insert-injective xs k y k₁' k₂'
        (Maybe.just-injective p₁)
        (Maybe.just-injective p₂)
    }

  delete-lookup
    : (xs : Object)
    → (k : Fin (List.length xs))
    → (k' : Fin (List.length xs))
    → Maybe (l ∈ Fin (List.length (List.delete xs k))
      × Category.Arrow C (xs ! k') (List.delete xs k ! l))
  delete-lookup (x ∷ xs) k k'
    with Fin.compare k' k
    | Fin.drop k'
    | inspect Fin.drop k'
  ... | τ₁ _ _ _ | nothing | _
    = nothing -- impossible
  ... | τ₁ p _ _ | just k'' | [ q ]
    = just (k''
      , rewrite'
        (Category.Arrow C ((x ∷ xs) ! k'))
        (List.lookup-delete-less x xs q p)
        (Category.identity C ((x ∷ xs) ! k')))
  ... | τ₂ _ _ _ | _ | _
    = nothing
  delete-lookup (x ∷ xs) k (suc k') | τ₃ p₁ p₂ _ | _ | _
    = just (k'
      , rewrite'
        (Category.Arrow C ((x ∷ xs) ! suc k'))
        (List.lookup-delete-¬less x xs k k' p₁ p₂)
        (Category.identity C (xs ! k')))

  delete-injective
    : (xs : Object)
    → (k : Fin (List.length xs))
    → (k₁' k₂' : Fin (List.length xs))
    → {l : Fin (List.length (List.delete xs k))}
    → {f₁ : Category.Arrow C (xs ! k₁') (List.delete xs k ! l)}
    → {f₂ : Category.Arrow C (xs ! k₂') (List.delete xs k ! l)}
    → delete-lookup xs k k₁' ≡ just (l , f₁)
    → delete-lookup xs k k₂' ≡ just (l , f₂)
    → k₁' ≡ k₂'
  delete-injective (_ ∷ _) k k₁' k₂' _ _
    with Fin.compare k₁' k
    | Fin.compare k₂' k
    | Fin.drop k₁'
    | inspect Fin.drop k₁'
    | Fin.drop k₂'
    | inspect Fin.drop k₂'

  delete-injective _ _ k₁' k₂' refl refl
    | τ₁ _ _ _ | τ₁ _ _ _ | just _ | [ q₁ ] | just _ | [ q₂ ]
    = trans (Fin.drop-just k₁' q₁) (sym (Fin.drop-just k₂' q₂))
  delete-injective _ _ (suc _) (suc _) refl refl
    | τ₃ _ _ _ | τ₃ _ _ _ | _ | _ | _ | _
    = refl

  delete-injective _ _ k₁' (suc _) refl refl
    | τ₁ p₁ _ _ | τ₃ _ _ p₂ | just _ | [ q₁ ] | _ | _
    with Fin.drop-just k₁' q₁
  ... | refl
    = ⊥-elim (Fin.<-¬suc p₁ p₂)
  delete-injective _ _ (suc _) k₂' refl refl
    | τ₃ _ _ p₁ | τ₁ p₂ _ _ | _ | _ | just _ | [ q₂ ]
    with Fin.drop-just k₂' q₂
  ... | refl
    = ⊥-elim (Fin.<-¬suc p₂ p₁)

  delete
    : (xs : Object)
    → (k : Fin (List.length xs))
    → Arrow xs (List.delete xs k)
  delete xs k
    = record
    { lookup
      = delete-lookup xs k
    ; injective
      = delete-injective xs k
    }

  swap-lookup
    : (x : Category.Object C)
    → (xs : Object)
    → (k : Fin (List.length xs))
    → (k' : Fin (List.length (x ∷ xs)))
    → l ∈ Fin (List.length (x ∷ xs))
    × Category.Arrow C ((x ∷ xs) ! k') (List.swap x xs k ! l)
  swap-lookup x xs k k'
    with Fin.compare k' (Fin.lift k)
    | Fin.compare k' (suc k)
  ... | τ₁ p _ _ | _
    = (k' , rewrite'
      (Category.Arrow C ((x ∷ xs) ! k'))
      (List.lookup-swap-less x xs k p)
      (Category.identity C ((x ∷ xs) ! k')))
  ... | τ₂ _ refl _ | _
    = (suc k , rewrite'
      (Category.Arrow C ((x ∷ xs) ! Fin.lift k))
      (List.lookup-swap₂ x xs k)
      (Category.identity C ((x ∷ xs) ! Fin.lift k)))
  ... | _ | τ₂ _ refl _
    = (Fin.lift k , rewrite'
      (Category.Arrow C ((x ∷ xs) ! suc k))
      (List.lookup-swap₁ x xs k)
      (Category.identity C ((x ∷ xs) ! suc k)))
  ... | _ | τ₃ _ _ p
    = (k' , rewrite'
      (Category.Arrow C ((x ∷ xs) ! k'))
      (List.lookup-swap-greater x xs p)
      (Category.identity C ((x ∷ xs) ! k')))
  ... | τ₃ _ _ p | τ₁ q _ _
    = ⊥-elim (Fin.<-¬suc p q)

  swap-injective
    : (x : Category.Object C)
    → (xs : Object)
    → (k : Fin (List.length xs))
    → (k₁' k₂' : Fin (List.length (x ∷ xs)))
    → {l : Fin (List.length (x ∷ xs))}
    → {f₁ : Category.Arrow C ((x ∷ xs) ! k₁') (List.swap x xs k ! l)}
    → {f₂ : Category.Arrow C ((x ∷ xs) ! k₂') (List.swap x xs k ! l)}
    → swap-lookup x xs k k₁' ≡ (l , f₁)
    → swap-lookup x xs k k₂' ≡ (l , f₂)
    → k₁' ≡ k₂'
  swap-injective _ _ k k₁' k₂' _ _
    with Fin.compare k₁' (Fin.lift k)
    | Fin.compare k₁' (suc k)
    | Fin.compare k₂' (Fin.lift k)
    | Fin.compare k₂' (suc k)

  swap-injective _ _ _ _ _ refl refl
    | τ₁ _ _ _ | _ | τ₁ _ _ _ | _
    = refl
  swap-injective _ _ k _ _ refl refl
    | τ₁ _ _ ¬p | _ | τ₂ _ refl _ | _
    = ⊥-elim (¬p (Fin.<-suc k))
  swap-injective _ _ _ _ _ refl refl
    | τ₁ _ ¬p _ | _ | τ₃ _ _ _ | τ₂ _ refl _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₁ _ _ _ | _ | τ₃ _ _ _ | τ₃ _ _ _
    = refl
  swap-injective _ _ k _ _ refl refl
    | τ₂ _ refl _ | _ | τ₁ _ _ ¬p | _
    = ⊥-elim (¬p (Fin.<-suc k))
  swap-injective _ _ _ _ _ _ _
    | τ₂ _ refl _ | _ | τ₂ _ refl _ | _
    = refl
  swap-injective _ _ _ _ _ p₁ p₂
    | τ₂ _ refl _ | _ | τ₃ _ _ _ | τ₂ _ refl _
    = trans (Sigma.comma-injective₁ p₂) (Sigma.comma-injective₁ (sym p₁))
  swap-injective _ _ _ _ _ refl refl
    | τ₂ _ refl _ | _ | τ₃ _ _ _ | τ₃ _ ¬p _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₂ _ refl _ | τ₁ _ ¬p _ | _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ p₁ p₂
    | τ₃ _ _ _ | τ₂ _ refl _ | τ₂ _ refl _ | _
    = trans (Sigma.comma-injective₁ p₂) (Sigma.comma-injective₁ (sym p₁))
  swap-injective _ _ _ _ _ _ _
    | τ₃ _ _ _ | τ₂ _ refl _ | τ₃ _ _ _ | τ₂ _ refl _
    = refl
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₂ _ refl _ | τ₃ _ ¬p _ | τ₃ _ _ _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₃ _ _ _ | τ₁ _ _ _ | _
    = refl
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₃ _ ¬p _ | τ₂ _ refl _ | _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ ¬p _ | τ₃ _ _ _ | τ₃ _ _ _ | τ₂ _ refl _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₃ _ _ _ | τ₃ _ _ _ | τ₃ _ _ _
    = refl

  ... | τ₃ _ _ p | τ₁ q _ _ | _ | _
    = ⊥-elim (Fin.<-¬suc p q)
  ... | _ | _ | τ₃ _ _ p | τ₁ q _ _
    = ⊥-elim (Fin.<-¬suc p q)

  swap
    : (x : Category.Object C)
    → (xs : Object)
    → (k : Fin (List.length xs))
    → Arrow (x ∷ xs) (List.swap x xs k)
  swap x xs k
    = record
    { lookup
      = λ k'
      → just
        (swap-lookup x xs k k')
    ; injective
      = λ k₁' k₂' p₁ p₂
      → swap-injective x xs k k₁' k₂'
        (Maybe.just-injective p₁)
        (Maybe.just-injective p₂)
    }

category-list
  : Category
  → Category
category-list C
  = record {CategoryList C}

-- ### Equality

arrow-equal-list
  : (C : Category)
  → {m n : ℕ}
  → {xs₁ xs₂ : Vec (Category.Object C) m}
  → {ys₁ ys₂ : Vec (Category.Object C) n}
  → {fs₁ : Category.Arrow (category-list C) (any xs₁) (any ys₁)}
  → {fs₂ : Category.Arrow (category-list C) (any xs₂) (any ys₂)}
  → xs₁ ≡ xs₂
  → ys₁ ≡ ys₂
  → ((k : Fin m) → CategoryList.LookupEqual' C xs₁ xs₂ ys₁ ys₂ k
    (CategoryList.Arrow.lookup fs₁ k)
    (CategoryList.Arrow.lookup fs₂ k))
  → Category.ArrowEqual' (category-list C) fs₁ fs₂
arrow-equal-list C refl refl f
  = Category.any
  $ record
  { lookup
    = λ k → CategoryList.lookup-equal' C (f k)
  }

-- ## Functor

-- ### Function

module _
  {C D : Category}
  where

  module FunctorList
    (F : Functor C D)
    where

    base
      : Category.Object (category-list C)
      → Category.Object (category-list D)
    base
      = List.map
        (Functor.base F)

    map-lookup
      : {xs ys : Category.Object (category-list C)}
      → Category.Arrow (category-list C) xs ys
      → (k : Fin (List.length (base xs)))
      → Maybe (l ∈ Fin (List.length (base ys))
        × Category.Arrow D (base xs ! k) (base ys ! l))
    map-lookup {xs = xs} {ys = ys} fs k
      with CategoryList.Arrow.lookup fs k
    ... | nothing
      = nothing
    ... | just (l , g)
      = just (l , Category.arrow D
        (List.lookup-map (Functor.base F) xs k)
        (List.lookup-map (Functor.base F) ys l)
        (Functor.map F g))

    abstract

      map-injective
        : {xs ys : Category.Object (category-list C)}
        → (fs : Category.Arrow (category-list C) xs ys)
        → (k₁ k₂ : Fin (List.length (base xs)))
        → {l : Fin (List.length (base ys))}
        → {f₁ : Category.Arrow D (base xs ! k₁) (base ys ! l)}
        → {f₂ : Category.Arrow D (base xs ! k₂) (base ys ! l)}
        → map-lookup fs k₁ ≡ just (l , f₁)
        → map-lookup fs k₂ ≡ just (l , f₂)
        → k₁ ≡ k₂
      map-injective fs k₁ k₂ _ _
        with CategoryList.Arrow.lookup fs k₁
        | inspect (CategoryList.Arrow.lookup fs) k₁
        | CategoryList.Arrow.lookup fs k₂
        | inspect (CategoryList.Arrow.lookup fs) k₂
      map-injective fs k₁ k₂ refl refl | just _ | [ p₁ ] | just _ | [ p₂ ]
        = CategoryList.Arrow.injective fs k₁ k₂ p₁ p₂

    map
      : {xs ys : Category.Object (category-list C)}
      → Category.Arrow (category-list C) xs ys
      → Category.Arrow (category-list D) (base xs) (base ys)
    map fs
      = record
      { lookup
        = map-lookup fs
      ; injective
        = map-injective fs
      }

    abstract

      map-equal-lookup
        : {xs ys : Category.Object (category-list C)}
        → {fs₁ fs₂ : Category.Arrow (category-list C) xs ys}
        → Category.ArrowEqual (category-list C) fs₁ fs₂
        → (k : Fin (List.length xs))
        → CategoryList.LookupEqual D (base xs) (base ys) k
          (map-lookup fs₁ k)
          (map-lookup fs₂ k)
      map-equal-lookup {xs = xs} {ys = ys} {fs₁ = fs₁} {fs₂ = fs₂} ps k
        with CategoryList.Arrow.lookup fs₁ k
        | CategoryList.Arrow.lookup fs₂ k
        | CategoryList.ArrowEqual.lookup ps k
      ... | _ | _ | CategoryList.nothing
        = CategoryList.nothing
      ... | _ | _ | CategoryList.just l q
        = CategoryList.just l
        $ Category.arrow-equal D
          (List.lookup-map (Functor.base F) xs k)
          (List.lookup-map (Functor.base F) ys l)
          (Functor.map-equal F q)

      map-equal
        : {xs ys : Category.Object (category-list C)}
        → {fs₁ fs₂ : Category.Arrow (category-list C) xs ys}
        → Category.ArrowEqual (category-list C) fs₁ fs₂
        → Category.ArrowEqual (category-list D) (map fs₁) (map fs₂)
      map-equal ps
        = record
        { lookup
          = map-equal-lookup ps
        }

      map-identity-lookup
        : (xs : Category.Object (category-list C))
        → (k : Fin (List.length xs))
        → CategoryList.LookupEqual D (base xs) (base xs) k
          (map-lookup (Category.identity (category-list C) xs) k)
          (CategoryList.identity-lookup D (base xs) k)
      map-identity-lookup xs k
        = CategoryList.just k
        $ Category.any' D
        $ Category.arrow-trans' D (Category.arrow-equal' D p p
          (Functor.map F (Category.identity C (xs ! k))))
        $ Category.arrow-trans' D (Functor.map-identity' F (xs ! k))
        $ Category.identity-equal D (sym p)
        where
          p = List.lookup-map (Functor.base F) xs k

      map-identity
        : (xs : Category.Object (category-list C))
        → Category.ArrowEqual (category-list D)
          (map (Category.identity (category-list C) xs))
          (Category.identity (category-list D) (base xs))
      map-identity xs
        = record
        { lookup
          = map-identity-lookup xs
        }

      map-compose-lookup
        : {xs ys zs : Category.Object (category-list C)}
        → (fs : Category.Arrow (category-list C) ys zs)
        → (gs : Category.Arrow (category-list C) xs ys)
        → (k : Fin (List.length xs))
        → CategoryList.LookupEqual D (base xs) (base zs) k
          (map-lookup (Category.compose (category-list C) fs gs) k)
          (CategoryList.compose-lookup D (map fs) (map gs) k)
      map-compose-lookup {xs = xs} {ys = ys} {zs = zs} fs gs k
        with CategoryList.Arrow.lookup gs k
      ... | nothing
        = CategoryList.nothing
      ... | just (l , g)
        with CategoryList.Arrow.lookup fs l
      ... | nothing
        = CategoryList.nothing
      ... | just (m , f)
        = CategoryList.just m
        $ Category.any' D
        $ Category.arrow-trans' D (Category.arrow-equal' D p r
          (Functor.map F (Category.compose C f g)))
        $ Category.arrow-trans' D (Functor.map-compose' F f g)
        $ Category.arrow-sym' D (Category.compose-equal' D
          (Category.arrow-equal' D q r (Functor.map F f)) 
          (Category.arrow-equal' D p q (Functor.map F g)))
        where
          p = List.lookup-map (Functor.base F) xs k
          q = List.lookup-map (Functor.base F) ys l
          r = List.lookup-map (Functor.base F) zs m

      map-compose
        : {xs ys zs : Category.Object (category-list C)}
        → (fs : Category.Arrow (category-list C) ys zs)
        → (gs : Category.Arrow (category-list C) xs ys)
        → Category.ArrowEqual (category-list D)
          (map (Category.compose (category-list C) fs gs))
          (Category.compose (category-list D) (map fs) (map gs))
      map-compose fs gs
        = record
        { lookup
          = map-compose-lookup fs gs
        }

  functor-list
    : Functor C D
    → Functor
      (category-list C)
      (category-list D)
  functor-list F
    = record {FunctorList F}

-- ### Identity

module FunctorListIdentity
  (C : Category)
  where

  base'
    : {n : ℕ}
    → (xs : Vec (Category.Object C) n)
    → Vec.map id xs ≡ xs
  base'
    = Vec.map-identity

  base
    : (xs : Category.Object (category-list C))
    → Functor.base (functor-list (functor-identity' C)) xs
      ≅ Functor.base (functor-identity' (category-list C)) xs
  base
    = List.map-identity

  map'
    : {xs ys : Category.Object (category-list C)}
    → (fs : Category.Arrow (category-list C) xs ys)
    → (k : Fin (List.length xs))
    → CategoryList.LookupEqual' C
      (Any.value (Functor.base
        (functor-list (functor-identity' C)) xs))
      (Any.value (Functor.base
        (functor-identity' (category-list C)) xs))
      (Any.value (Functor.base
        (functor-list (functor-identity' C)) ys))
      (Any.value (Functor.base
        (functor-identity' (category-list C)) ys)) k
      (CategoryList.Arrow.lookup (Functor.map
        (functor-list (functor-identity' C)) fs) k)
      (CategoryList.Arrow.lookup (Functor.map
        (functor-identity' (category-list C)) fs) k)
  map' {xs = any xs} {ys = any ys} fs k
    with CategoryList.Arrow.lookup fs k
  ... | nothing
    = CategoryList.nothing'
  ... | just (l , f)
    = CategoryList.just' l
    $ Category.arrow-equal' C
      (Vec.lookup-map id xs k)
      (Vec.lookup-map id ys l) f

  map
    : {xs ys : Category.Object (category-list C)}
    → (fs : Category.Arrow (category-list C) xs ys)
    → Category'.ArrowEqual'
      (category-list C)
      (category-list C)
      (Functor.map (functor-list (functor-identity' C)) fs)
      (Functor.map (functor-identity' (category-list C)) fs)
  map {xs = any xs} {ys = any ys} fs
    = arrow-equal-list C (base' xs) (base' ys) (map' fs)

functor-list-identity
  : (C : Category)
  → FunctorEqual
    (functor-list (functor-identity' C))
    (functor-identity' (category-list C))
functor-list-identity C
  = record {FunctorListIdentity C}

-- ### Compose

module _
  {C D E : Category}
  where

  module FunctorListCompose
    (F : Functor D E)
    (G : Functor C D)
    where

    base'
      : {n : ℕ}
      → (xs : Vec (Category.Object C) n)
      → Vec.map (Functor.base F ∘ Functor.base G) xs
        ≡ Vec.map (Functor.base F) (Vec.map (Functor.base G) xs)
    base'
      = Vec.map-compose
        (Functor.base F)
        (Functor.base G)

    base
      : (xs : Category.Object (category-list C))
      → Functor.base (functor-list (functor-compose' F G)) xs
        ≅ Functor.base (functor-compose' (functor-list F) (functor-list G)) xs
    base
      = List.map-compose
        (Functor.base F)
        (Functor.base G)
  
    map'
      : {xs ys : Category.Object (category-list C)}
      → (fs : Category.Arrow (category-list C) xs ys)
      → (k : Fin (List.length xs))
      → CategoryList.LookupEqual' E
        (Any.value (Functor.base
          (functor-list (functor-compose' F G)) xs))
        (Any.value (Functor.base
          (functor-compose' (functor-list F) (functor-list G)) xs))
        (Any.value (Functor.base
          (functor-list (functor-compose' F G)) ys))
        (Any.value (Functor.base
          (functor-compose' (functor-list F) (functor-list G)) ys)) k
        (CategoryList.Arrow.lookup (Functor.map
          (functor-list (functor-compose' F G)) fs) k)
        (CategoryList.Arrow.lookup (Functor.map
          (functor-compose' (functor-list F) (functor-list G)) fs) k)
    map' {xs = any xs} {ys = any ys} fs k
      with CategoryList.Arrow.lookup fs k
    ... | nothing
      = CategoryList.nothing'
    ... | just (l , f)
      = CategoryList.just' l
      $ Category.arrow-trans' E (Category.arrow-equal' E p'' q''
        (Functor.map F (Functor.map G f)))
      $ Category.arrow-trans' E (Category.arrow-sym' E
        (Functor.map-equal' F (Category.arrow-equal' D p q (Functor.map G f))))
      $ Category.arrow-sym' E (Category.arrow-equal' E p' q'
        (Functor.map F (Category.arrow D p q (Functor.map G f))))
      where
        p = Vec.lookup-map (Functor.base G) xs k
        q = Vec.lookup-map (Functor.base G) ys l
        p' = Vec.lookup-map (Functor.base F) (Vec.map (Functor.base G) xs) k
        q' = Vec.lookup-map (Functor.base F) (Vec.map (Functor.base G) ys) l
        p'' = Vec.lookup-map (Functor.base F ∘ Functor.base G) xs k
        q'' = Vec.lookup-map (Functor.base F ∘ Functor.base G) ys l

    map
      : {xs ys : Category.Object (category-list C)}
      → (fs : Category.Arrow (category-list C) xs ys)
      → Category'.ArrowEqual'
        (category-list E)
        (category-list E)
        (Functor.map (functor-list (functor-compose' F G)) fs)
        (Functor.map (functor-compose' (functor-list F) (functor-list G)) fs)
    map {xs = any xs} {ys = any ys} fs
      = arrow-equal-list E (base' xs) (base' ys) (map' fs)

  functor-list-compose
    : (F : Functor D E)
    → (G : Functor C D)
    → FunctorEqual
      (functor-list (functor-compose' F G))
      (functor-compose' (functor-list F) (functor-list G))
  functor-list-compose F G
    = record {FunctorListCompose F G}

-- ## FunctorEqual

module _
  {C D : Category}
  {F₁ F₂ : Functor C D}
  where

  module FunctorEqualList
    (p : FunctorEqual F₁ F₂)
    where

    base'
      : {n : ℕ}
      → (xs : Vec (Category.Object C) n)
      → Vec.map (Functor.base F₁) xs
        ≡ Vec.map (Functor.base F₂) xs
    base'
      = Vec.map-equal
        (Functor.base F₁)
        (Functor.base F₂)
        (FunctorEqual.base p)

    base
      : (xs : Category.Object (category-list C))
      → Functor.base (functor-list F₁) xs ≅ Functor.base (functor-list F₂) xs
    base
      = List.map-equal
        (Functor.base F₁)
        (Functor.base F₂)
        (FunctorEqual.base p)
  
    map'
      : {xs ys : Category.Object (category-list C)}
      → (fs : Category.Arrow (category-list C) xs ys)
      → (k : Fin (List.length xs))
      → CategoryList.LookupEqual' D
        (Any.value (Functor.base
          (functor-list F₁) xs))
        (Any.value (Functor.base
          (functor-list F₂) xs))
        (Any.value (Functor.base
          (functor-list F₁) ys))
        (Any.value (Functor.base
          (functor-list F₂) ys)) k
        (CategoryList.Arrow.lookup (Functor.map
          (functor-list F₁) fs) k)
        (CategoryList.Arrow.lookup (Functor.map
          (functor-list F₂) fs) k)
    map' {xs = any xs} {ys = any ys} fs k
      with CategoryList.Arrow.lookup fs k
    ... | nothing
      = CategoryList.nothing'
    ... | just (l , f)
      = CategoryList.just' l
      $ Category.arrow-trans' D (Category.arrow-equal' D p₁ q₁
        (Functor.map F₁ f))
      $ Category.arrow-trans' D (FunctorEqual.map p f)
      $ Category.arrow-sym' D (Category.arrow-equal' D p₂ q₂
        (Functor.map F₂ f))
      where
        p₁ = Vec.lookup-map (Functor.base F₁) xs k
        p₂ = Vec.lookup-map (Functor.base F₂) xs k
        q₁ = Vec.lookup-map (Functor.base F₁) ys l
        q₂ = Vec.lookup-map (Functor.base F₂) ys l

    map
      : {xs ys : Category.Object (category-list C)}
      → (fs : Category.Arrow (category-list C) xs ys)
      → Category'.ArrowEqual'
        (category-list D)
        (category-list D)
        (Functor.map (functor-list F₁) fs)
        (Functor.map (functor-list F₂) fs)
    map {xs = any xs} {ys = any ys} fs
      = arrow-equal-list D (base' xs) (base' ys) (map' fs)

  functor-equal-list
    : FunctorEqual F₁ F₂
    → FunctorEqual
      (functor-list F₁)
      (functor-list F₂)
  functor-equal-list p
    = record {FunctorEqualList p}

-- ## FunctorIdentity

functor-identity-list
  : {C : Category}
  → {F : Functor C C}
  → FunctorIdentity F
  → FunctorIdentity
    (functor-list F)
functor-identity-list {C = C} p
  = functor-identity-from-equal
  $ functor-trans (functor-equal-list
    (functor-identity-to-equal p))
  $ functor-list-identity C

-- ## FunctorCompose

functor-compose-list
  : {C D E : Category}
  → {F : Functor D E}
  → {G : Functor C D}
  → {H : Functor C E}
  → FunctorCompose F G H
  → FunctorCompose
    (functor-list F)
    (functor-list G)
    (functor-list H)
functor-compose-list {F = F} {G = G} p
  = functor-compose-from-equal
    (functor-list F)
    (functor-list G)
  $ functor-trans (functor-equal-list
    (functor-compose-to-equal p))
  $ functor-list-compose F G

-- ## FunctorSquare

functor-square-list
  : {C₁ C₂ D₁ D₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → FunctorSquare F G H₁ H₂
  → FunctorSquare
    (functor-list F)
    (functor-list G)
    (functor-list H₁)
    (functor-list H₂)
functor-square-list {F = F} {G = G} {H₁ = H₁} {H₂ = H₂} s
  = functor-square-from-equal
    (functor-list F)
    (functor-list G)
    (functor-list H₁)
    (functor-list H₂)
  $ functor-trans (functor-sym
    (functor-list-compose H₂ F))
  $ functor-trans (functor-equal-list
    (functor-square-to-equal s))
  $ functor-list-compose G H₁

