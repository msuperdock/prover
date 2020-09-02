module Prover.Category.Setoid.List where

open import Prover.Category
  using (Category; Functor; FunctorCompose; FunctorEqual; FunctorIdentity;
    FunctorSquare; functor-compose'; functor-compose-to-equal;
    functor-identity'; functor-identity-to-equal; functor-square-to-equal)
open import Prover.Category.Setoid
  using (SetoidCategory; SetoidFunctor; SetoidFunctorCompose;
    SetoidFunctorEqual; SetoidFunctorIdentity; SetoidFunctorSquare;
    setoid-functor-compose; setoid-functor-compose-from-equal;
    setoid-functor-identity; setoid-functor-identity-from-equal;
    setoid-functor-square-from-equal; setoid-functor-sym; setoid-functor-trans)
open import Prover.Prelude

open List
  using (_∷_; _!_)

-- ## SetoidCategory

-- ### Function

module SetoidCategoryList
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
    → (k₁ k₂ : Fin (List.length xs))
    → {l : Fin (suc (List.length xs))}
    → {f₁ : Category.Arrow C (xs ! k₁) (List.insert xs k y ! l)}
    → {f₂ : Category.Arrow C (xs ! k₂) (List.insert xs k y ! l)}
    → insert-lookup xs k y k₁ ≡ (l , f₁)
    → insert-lookup xs k y k₂ ≡ (l , f₂)
    → k₁ ≡ k₂
  insert-injective _ k _ k₁ k₂ p₁ p₂
    with Fin.compare (Fin.lift k₁) k
    | Fin.compare (Fin.lift k₂) k
    | Sigma.comma-injective₁ p₁
    | Sigma.comma-injective₁ p₂

  ... | τ₁ _ _ _ | τ₁ _ _ _ | q₁ | q₂
    = Fin.lift-injective k₁ k₂ (trans q₁ (sym q₂))
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
      (Fin.<-trans r₁ (Fin.<-suc k₂)))
  ... | τ₁ r₁ _ _ | τ₃ _ _ r₂ | refl | q₂
    = ⊥-elim (Fin.<-¬refl' (sym q₂)
      (Fin.<-trans r₁ (Fin.<-trans r₂ (Fin.<-suc k₂))))
  ... | τ₂ _ refl _ | τ₁ r₁ _ _ | q₁ | refl
    = ⊥-elim (Fin.<-¬refl' (sym q₁)
      (Fin.<-trans r₁ (Fin.<-suc k₁)))
  ... | τ₃ _ _ r₁ | τ₁ r₂ _ _ | q₁ | refl
    = ⊥-elim (Fin.<-¬refl' (sym q₁)
      (Fin.<-trans r₂ (Fin.<-trans r₁ (Fin.<-suc k₁))))

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
      = λ k₁ k₂ p₁ p₂
      → insert-injective xs k y k₁ k₂
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
    → (k₁ k₂ : Fin (List.length xs))
    → {l : Fin (List.length (List.delete xs k))}
    → {f₁ : Category.Arrow C (xs ! k₁) (List.delete xs k ! l)}
    → {f₂ : Category.Arrow C (xs ! k₂) (List.delete xs k ! l)}
    → delete-lookup xs k k₁ ≡ just (l , f₁)
    → delete-lookup xs k k₂ ≡ just (l , f₂)
    → k₁ ≡ k₂
  delete-injective (_ ∷ _) k k₁ k₂ _ _
    with Fin.compare k₁ k
    | Fin.compare k₂ k
    | Fin.drop k₁
    | inspect Fin.drop k₁
    | Fin.drop k₂
    | inspect Fin.drop k₂

  delete-injective _ _ k₁ k₂ refl refl
    | τ₁ _ _ _ | τ₁ _ _ _ | just _ | [ q₁ ] | just _ | [ q₂ ]
    = trans (Fin.drop-just k₁ q₁) (sym (Fin.drop-just k₂ q₂))
  delete-injective _ _ (suc _) (suc _) refl refl
    | τ₃ _ _ _ | τ₃ _ _ _ | _ | _ | _ | _
    = refl

  delete-injective _ _ k₁ (suc _) refl refl
    | τ₁ p₁ _ _ | τ₃ _ _ p₂ | just _ | [ q₁ ] | _ | _
    with Fin.drop-just k₁ q₁
  ... | refl
    = ⊥-elim (Fin.<-¬suc p₁ p₂)
  delete-injective _ _ (suc _) k₂ refl refl
    | τ₃ _ _ p₁ | τ₁ p₂ _ _ | _ | _ | just _ | [ q₂ ]
    with Fin.drop-just k₂ q₂
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
    → (k₁ k₂ : Fin (List.length (x ∷ xs)))
    → {l : Fin (List.length (x ∷ xs))}
    → {f₁ : Category.Arrow C ((x ∷ xs) ! k₁) (List.swap x xs k ! l)}
    → {f₂ : Category.Arrow C ((x ∷ xs) ! k₂) (List.swap x xs k ! l)}
    → swap-lookup x xs k k₁ ≡ (l , f₁)
    → swap-lookup x xs k k₂ ≡ (l , f₂)
    → k₁ ≡ k₂
  swap-injective _ _ k k₁ k₂ _ _
    with Fin.compare k₁ (Fin.lift k)
    | Fin.compare k₁ (suc k)
    | Fin.compare k₂ (Fin.lift k)
    | Fin.compare k₂ (suc k)

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
      = λ k₁ k₂ p₁ p₂
      → swap-injective x xs k k₁ k₂
        (Maybe.just-injective p₁)
        (Maybe.just-injective p₂)
    }

  record ArrowEqual
    {xs ys : Object}
    (fs₁ fs₂ : Arrow xs ys)
    : Set
    where

    constructor

      arrow-equal

    field

      lookup
        : (k : Fin (List.length xs))
        → Arrow.lookup fs₁ k ≡ Arrow.lookup fs₂ k

  arrow-refl
    : {xs ys : Object}
    → {fs : Arrow xs ys}
    → ArrowEqual fs fs
  arrow-refl
    = arrow-equal (λ _ → refl)

  arrow-sym
    : {xs ys : Object}
    → {fs₁ fs₂ : Arrow xs ys}
    → ArrowEqual fs₁ fs₂
    → ArrowEqual fs₂ fs₁
  arrow-sym (arrow-equal f)
    = arrow-equal (λ k → sym (f k))

  arrow-trans
    : {xs ys : Object}
    → {fs₁ fs₂ fs₃ : Arrow xs ys}
    → ArrowEqual fs₁ fs₂
    → ArrowEqual fs₂ fs₃
    → ArrowEqual fs₁ fs₃
  arrow-trans (arrow-equal f₁) (arrow-equal f₂)
    = arrow-equal (λ k → trans (f₁ k) (f₂ k))

  ArrowSetoid
    : Object
    → Object
    → Setoid
  ArrowSetoid xs ys
    = record
    { Element
      = Arrow xs ys
    ; ElementEqual
      = ArrowEqual
    ; element-refl
      = arrow-refl
    ; element-sym
      = arrow-sym
    ; element-trans
      = arrow-trans
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

    compose-eq'
      : {xs ys zs : Object}
      → {fs₁ fs₂ : Arrow ys zs}
      → {gs₁ gs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual gs₁ gs₂
      → (k : Fin (List.length xs))
      → Arrow.lookup (compose fs₁ gs₁) k ≡ Arrow.lookup (compose fs₂ gs₂) k
    compose-eq' {fs₁ = fs₁} {fs₂ = fs₂} {gs₁ = gs₁} {gs₂ = gs₂} p q k
      with Arrow.lookup gs₁ k
      | Arrow.lookup gs₂ k
      | ArrowEqual.lookup q k
    ... | nothing | nothing | refl
      = refl
    ... | just (l , _) | just _ | refl
      with Arrow.lookup fs₁ l
      | Arrow.lookup fs₂ l
      | ArrowEqual.lookup p l
    ... | _ | _ | refl
      = refl

    compose-eq
      : {xs ys zs : Object}
      → {fs₁ fs₂ : Arrow ys zs}
      → {gs₁ gs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual gs₁ gs₂
      → ArrowEqual
        (compose fs₁ gs₁)
        (compose fs₂ gs₂)
    compose-eq p q
      = arrow-equal (compose-eq' p q)

    precompose'
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → (k : Fin (List.length xs))
      → Arrow.lookup (compose fs (identity xs)) k
      ≡ Arrow.lookup fs k
    precompose' fs k
      with Arrow.lookup fs k
    ... | nothing
      = refl
    ... | just (l , f)
      = sub (λ x → just (l , x))
        (Category.precompose C f)

    precompose
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (compose fs (identity xs)) fs
    precompose fs
      = arrow-equal (precompose' fs)

    postcompose'
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → (k : Fin (List.length xs))
      → Arrow.lookup (compose (identity ys) fs) k
      ≡ Arrow.lookup fs k
    postcompose' fs k
      with Arrow.lookup fs k
    ... | nothing
      = refl
    ... | just (l , f)
      = sub (λ x → just (l , x))
        (Category.postcompose C f)

    postcompose
      : {xs ys : Object}
      → (fs : Arrow xs ys)
      → ArrowEqual
        (compose (identity ys) fs) fs
    postcompose fs
      = arrow-equal (postcompose' fs)

    associative'
      : {ws xs ys zs : Object}
      → (fs : Arrow ys zs)
      → (gs : Arrow xs ys)
      → (hs : Arrow ws xs)
      → (k : Fin (List.length ws))
      → Arrow.lookup (compose (compose fs gs) hs) k
      ≡ Arrow.lookup (compose fs (compose gs hs)) k
    associative' fs gs hs k
      with Arrow.lookup hs k
    ... | nothing
      = refl
    ... | just (l , h)
      with Arrow.lookup gs l
    ... | nothing
      = refl
    ... | just (m , g)
      with Arrow.lookup fs m
    ... | nothing
      = refl
    ... | just (n , f)
      = sub (λ x → just (n , x))
        (Category.associative C f g h)

    associative
      : {ws xs ys zs : Object}
      → (fs : Arrow ys zs)
      → (gs : Arrow xs ys)
      → (hs : Arrow ws xs)
      → ArrowEqual
        (compose (compose fs gs) hs)
        (compose fs (compose gs hs))
    associative fs gs hs
      = arrow-equal (associative' fs gs hs)

setoid-category-list
  : Category
  → SetoidCategory
setoid-category-list C
  = record {SetoidCategoryList C}

-- ### Equality

setoid-category-list-arrow-equal'
  : (C : Category)
  → {m n : ℕ}
  → {xs₁ xs₂ : Vec (Category.Object C) m}
  → {ys₁ ys₂ : Vec (Category.Object C) n}
  → {fs₁ : SetoidCategory.Arrow (setoid-category-list C) (any xs₁) (any ys₁)}
  → {fs₂ : SetoidCategory.Arrow (setoid-category-list C) (any xs₂) (any ys₂)}
  → xs₁ ≡ xs₂
  → ys₁ ≡ ys₂
  → ((k : Fin m)
    → SetoidCategoryList.Arrow.lookup fs₁ k
    ≅ SetoidCategoryList.Arrow.lookup fs₂ k)
  → SetoidCategory.ArrowEqual' (setoid-category-list C) fs₁ fs₂
setoid-category-list-arrow-equal' _ refl refl p
  = SetoidCategory.arrow-equal'
    (SetoidCategoryList.arrow-equal p)

-- ## SetoidFunctor

-- ### Function

module _
  {C D : Category}
  where

  module SetoidFunctorList
    (F : Functor C D)
    where

    base
      : SetoidCategory.Object (setoid-category-list C)
      → SetoidCategory.Object (setoid-category-list D)
    base
      = List.map
        (Functor.base F)

    map-lookup
      : {xs ys : SetoidCategory.Object (setoid-category-list C)}
      → SetoidCategory.Arrow (setoid-category-list C) xs ys
      → (k : Fin (List.length (base xs)))
      → Maybe (l ∈ Fin (List.length (base ys))
        × Category.Arrow D (base xs ! k) (base ys ! l))
    map-lookup {xs = xs} {ys = ys} f k
      with SetoidCategoryList.Arrow.lookup f k
    ... | nothing
      = nothing
    ... | just (l , g)
      = just (l , Category.arrow D
        (List.lookup-map (Functor.base F) xs k)
        (List.lookup-map (Functor.base F) ys l)
        (Functor.map F g))

    abstract

      map-injective
        : {xs ys : SetoidCategory.Object (setoid-category-list C)}
        → (f : SetoidCategory.Arrow (setoid-category-list C) xs ys)
        → (k₁ k₂ : Fin (List.length (base xs)))
        → {l : Fin (List.length (base ys))}
        → {f₁ : Category.Arrow D (base xs ! k₁) (base ys ! l)}
        → {f₂ : Category.Arrow D (base xs ! k₂) (base ys ! l)}
        → map-lookup f k₁ ≡ just (l , f₁)
        → map-lookup f k₂ ≡ just (l , f₂)
        → k₁ ≡ k₂
      map-injective f k₁ k₂ _ _
        with SetoidCategoryList.Arrow.lookup f k₁
        | inspect (SetoidCategoryList.Arrow.lookup f) k₁
        | SetoidCategoryList.Arrow.lookup f k₂
        | inspect (SetoidCategoryList.Arrow.lookup f) k₂
      map-injective f k₁ k₂ refl refl | just _ | [ p₁ ] | just _ | [ p₂ ]
        = SetoidCategoryList.Arrow.injective f k₁ k₂ p₁ p₂

    map
      : {xs ys : SetoidCategory.Object (setoid-category-list C)}
      → SetoidCategory.Arrow (setoid-category-list C) xs ys
      → SetoidCategory.Arrow (setoid-category-list D) (base xs) (base ys)
    map fs
      = record
      { lookup
        = map-lookup fs
      ; injective
        = map-injective fs
      }

    abstract

      map-eq'
        : {xs ys : SetoidCategory.Object (setoid-category-list C)}
        → {fs₁ fs₂ : SetoidCategory.Arrow (setoid-category-list C) xs ys}
        → SetoidCategory.ArrowEqual (setoid-category-list C) fs₁ fs₂
        → (k : Fin (List.length xs))
        → map-lookup fs₁ k ≡ map-lookup fs₂ k
      map-eq' {fs₁ = fs₁} {fs₂ = fs₂} p k
        with SetoidCategoryList.Arrow.lookup fs₁ k
        | SetoidCategoryList.Arrow.lookup fs₂ k
        | SetoidCategoryList.ArrowEqual.lookup p k
      ... | _ | _ | refl
        = refl

      map-eq
        : {xs ys : SetoidCategory.Object (setoid-category-list C)}
        → {fs₁ fs₂ : SetoidCategory.Arrow (setoid-category-list C) xs ys}
        → SetoidCategory.ArrowEqual (setoid-category-list C) fs₁ fs₂
        → SetoidCategory.ArrowEqual (setoid-category-list D) (map fs₁) (map fs₂)
      map-eq p
        = SetoidCategoryList.arrow-equal (map-eq' p)

      map-identity'
        : (xs : SetoidCategory.Object (setoid-category-list C))
        → (k : Fin (List.length xs))
        → map-lookup (SetoidCategory.identity (setoid-category-list C) xs) k
          ≡ SetoidCategoryList.identity-lookup D (base xs) k
      map-identity' xs k
        = sub just
        $ Sigma.comma-eq refl
        $ trans (Category.arrow-eq D p p
          (Functor.map F (Category.identity C (xs ! k))))
        $ trans (Functor.map-identity F (xs ! k))
        $ sym (Category.identity-eq D p)
        where
          p = List.lookup-map (Functor.base F) xs k

      map-identity
        : (xs : SetoidCategory.Object (setoid-category-list C))
        → SetoidCategory.ArrowEqual (setoid-category-list D)
          (map (SetoidCategory.identity (setoid-category-list C) xs))
          (SetoidCategory.identity (setoid-category-list D) (base xs))
      map-identity x
        = SetoidCategoryList.arrow-equal (map-identity' x)

      map-compose'
        : {xs ys zs : SetoidCategory.Object (setoid-category-list C)}
        → (fs : SetoidCategory.Arrow (setoid-category-list C) ys zs)
        → (gs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
        → (k : Fin (List.length xs))
        → map-lookup (SetoidCategory.compose (setoid-category-list C) fs gs) k
          ≡ SetoidCategoryList.compose-lookup D (map fs) (map gs) k
      map-compose' {xs = xs} {ys = ys} {zs = zs} fs gs k
        with SetoidCategoryList.Arrow.lookup gs k
      ... | nothing
        = refl
      ... | just (l , g)
        with SetoidCategoryList.Arrow.lookup fs l
      ... | nothing
        = refl
      ... | just (m , f)
        = sub just
        $ Sigma.comma-eq refl
        $ trans (Category.arrow-eq D p r
          (Functor.map F (Category.compose C f g)))
        $ trans (Functor.map-compose F f g)
        $ sym (Category.compose-eq D p q r
          (Category.arrow-eq D q r (Functor.map F f))
          (Category.arrow-eq D p q (Functor.map F g)))
        where
          p = List.lookup-map (Functor.base F) xs k
          q = List.lookup-map (Functor.base F) ys l
          r = List.lookup-map (Functor.base F) zs m

      map-compose
        : {xs ys zs : SetoidCategory.Object (setoid-category-list C)}
        → (fs : SetoidCategory.Arrow (setoid-category-list C) ys zs)
        → (gs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
        → SetoidCategory.ArrowEqual (setoid-category-list D)
          (map (SetoidCategory.compose (setoid-category-list C) fs gs))
          (SetoidCategory.compose (setoid-category-list D) (map fs) (map gs))
      map-compose fs gs
        = SetoidCategoryList.arrow-equal (map-compose' fs gs)

  setoid-functor-list
    : Functor C D
    → SetoidFunctor
      (setoid-category-list C)
      (setoid-category-list D)
  setoid-functor-list F
    = record {SetoidFunctorList F}

-- ### Identity

module SetoidFunctorListIdentity
  (C : Category)
  where

  base'
    : {n : ℕ}
    → (xs : Vec (Category.Object C) n)
    → Vec.map id xs ≡ xs
  base'
    = Vec.map-identity

  base
    : (xs : SetoidCategory.Object (setoid-category-list C))
    → SetoidFunctor.base (setoid-functor-list
      (functor-identity' C)) xs
    ≡ SetoidFunctor.base (setoid-functor-identity
      (setoid-category-list C)) xs
  base
    = List.map-identity

  map'
    : {xs ys : SetoidCategory.Object (setoid-category-list C)}
    → (fs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
    → (k : Fin (List.length xs))
    → SetoidCategoryList.Arrow.lookup
      (SetoidFunctor.map (setoid-functor-list
        (functor-identity' C)) fs) k
    ≅ SetoidCategoryList.Arrow.lookup
      (SetoidFunctor.map (setoid-functor-identity
        (setoid-category-list C)) fs) k
  map' fs k
    with SetoidCategoryList.Arrow.lookup fs k
  map' {xs = any xs} {ys = any ys} _ _ | nothing
    with Vec.map id xs
    | Vec.map-identity xs
    | Vec.map id ys
    | Vec.map-identity ys
  ... | _ | refl | _ | refl
    = refl
  map' {xs = any xs} {ys = any ys} _ k | just (l , _)
    with Vec.map id xs
    | Vec.map-identity xs
    | Vec.map id ys
    | Vec.map-identity ys
    | Vec.lookup-map id xs k
    | Vec.lookup-map id ys l
  ... | _ | refl | _ | refl | refl | refl
    = refl

  map
    : {xs ys : SetoidCategory.Object (setoid-category-list C)}
    → (fs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
    → SetoidCategory.ArrowEqual' (setoid-category-list C)
      (SetoidFunctor.map (setoid-functor-list
        (functor-identity' C)) fs)
      (SetoidFunctor.map (setoid-functor-identity
        (setoid-category-list C)) fs)
  map {xs = any xs} {ys = any ys} fs
    = setoid-category-list-arrow-equal' C (base' xs) (base' ys) (map' fs)

setoid-functor-list-identity
  : (C : Category)
  → SetoidFunctorEqual
    (setoid-functor-list
      (functor-identity' C))
    (setoid-functor-identity
      (setoid-category-list C))
setoid-functor-list-identity C
  = record {SetoidFunctorListIdentity C}

-- ### Compose

module _
  {C D E : Category}
  where

  module SetoidFunctorListCompose
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
      : (xs : SetoidCategory.Object (setoid-category-list C))
      → SetoidFunctor.base (setoid-functor-list
        (functor-compose' F G)) xs
      ≡ SetoidFunctor.base (setoid-functor-compose
        (setoid-functor-list F)
        (setoid-functor-list G)) xs
    base
      = List.map-compose
        (Functor.base F)
        (Functor.base G)
    
    map'
      : {xs ys : SetoidCategory.Object (setoid-category-list C)}
      → (fs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
      → (k : Fin (List.length xs))
      → SetoidCategoryList.Arrow.lookup
        (SetoidFunctor.map (setoid-functor-list
          (functor-compose' F G)) fs) k
      ≅ SetoidCategoryList.Arrow.lookup
        (SetoidFunctor.map (setoid-functor-compose
          (setoid-functor-list F)
          (setoid-functor-list G)) fs) k
    map' fs k
      with SetoidCategoryList.Arrow.lookup fs k
    map' {xs = any xs} {ys = any ys} _ _ | nothing
      with Vec.map (Functor.base F ∘ Functor.base G) xs
      | Vec.map-compose (Functor.base F) (Functor.base G) xs
      | Vec.map (Functor.base F ∘ Functor.base G) ys
      | Vec.map-compose (Functor.base F) (Functor.base G) ys
    ... | _ | refl | _ | refl
      = refl
    map' {xs = any xs} {ys = any ys} _ k | just (l , f)
      with Vec.map (Functor.base F ∘ Functor.base G) xs
      | Vec.map-compose (Functor.base F) (Functor.base G) xs
      | Vec.map (Functor.base F ∘ Functor.base G) ys
      | Vec.map-compose (Functor.base F) (Functor.base G) ys
      | Vec.lookup-map (Functor.base F ∘ Functor.base G) xs k
      | Vec.lookup-map (Functor.base F ∘ Functor.base G) ys l
      | Vec.lookup-map (Functor.base F) (Vec.map (Functor.base G) xs) k
      | Vec.lookup-map (Functor.base F) (Vec.map (Functor.base G) ys) l
      | Vec.lookup-map (Functor.base G) xs k
      | Vec.lookup-map (Functor.base G) ys l
    ... | _ | refl | _ | refl | p | q | p' | q' | p'' | q''
      = sub just
      $ Sigma.comma-eq refl
      $ trans (Category.arrow-eq E p q
        (Functor.map F (Functor.map G f)))
      $ trans (sym (Functor.map-eq F
        (Vec.lookup-map (Functor.base G) xs k)
        (Vec.lookup-map (Functor.base G) ys l)
        (Category.arrow-eq D p'' q'' (Functor.map G f))))
      $ sym (Category.arrow-eq E p' q'
        (Functor.map F (Category.arrow D p'' q'' (Functor.map G f))))

    map
      : {xs ys : SetoidCategory.Object (setoid-category-list C)}
      → (fs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
      → SetoidCategory.ArrowEqual' (setoid-category-list E)
        (SetoidFunctor.map (setoid-functor-list
          (functor-compose' F G)) fs)
        (SetoidFunctor.map (setoid-functor-compose
          (setoid-functor-list F)
          (setoid-functor-list G)) fs)
    map {xs = any xs} {ys = any ys} fs
      = setoid-category-list-arrow-equal' E (base' xs) (base' ys) (map' fs)

  setoid-functor-list-compose
    : (F : Functor D E)
    → (G : Functor C D)
    → SetoidFunctorEqual
      (setoid-functor-list
        (functor-compose' F G))
      (setoid-functor-compose
        (setoid-functor-list F)
        (setoid-functor-list G))
  setoid-functor-list-compose F G
    = record {SetoidFunctorListCompose F G}

-- ## SetoidFunctorEqual

module _
  {C D : Category}
  {F₁ F₂ : Functor C D}
  where

  module SetoidFunctorEqualList
    (p : FunctorEqual F₁ F₂)
    where

    base'
      : {n : ℕ}
      → (xs : Vec (Category.Object C) n)
      → Vec.map (Functor.base F₁) xs
        ≡ Vec.map (Functor.base F₂) xs
    base'
      = Vec.map-eq
        (Functor.base F₁)
        (Functor.base F₂)
        (FunctorEqual.base p)

    base
      : (xs : SetoidCategory.Object (setoid-category-list C))
      → SetoidFunctor.base (setoid-functor-list F₁) xs
        ≡ SetoidFunctor.base (setoid-functor-list F₂) xs
    base
      = List.map-eq
        (Functor.base F₁)
        (Functor.base F₂)
        (FunctorEqual.base p)
    
    map'
      : {xs ys : SetoidCategory.Object (setoid-category-list C)}
      → (fs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
      → (k : Fin (List.length xs))
      → SetoidCategoryList.Arrow.lookup
        (SetoidFunctor.map (setoid-functor-list F₁) fs) k
      ≅ SetoidCategoryList.Arrow.lookup
        (SetoidFunctor.map (setoid-functor-list F₂) fs) k
    map' fs k
      with SetoidCategoryList.Arrow.lookup fs k
    map' {xs = any xs} {ys = any ys} _ _ | nothing
      with Vec.map (Functor.base F₁) xs
      | Vec.map-eq (Functor.base F₁) (Functor.base F₂) (FunctorEqual.base p) xs
      | Vec.map (Functor.base F₁) ys
      | Vec.map-eq (Functor.base F₁) (Functor.base F₂) (FunctorEqual.base p) ys
    ... | _ | refl | _ | refl
      = refl
    map' {xs = any xs} {ys = any ys} _ k | just (l , f)
      with Vec.map (Functor.base F₁) xs
      | Vec.map-eq (Functor.base F₁) (Functor.base F₂) (FunctorEqual.base p) xs
      | Vec.map (Functor.base F₁) ys
      | Vec.map-eq (Functor.base F₁) (Functor.base F₂) (FunctorEqual.base p) ys
      | Vec.lookup-map (Functor.base F₁) xs k
      | Vec.lookup-map (Functor.base F₂) xs k
      | Vec.lookup-map (Functor.base F₁) ys l
      | Vec.lookup-map (Functor.base F₂) ys l
    ... | _ | refl | _ | refl | p₁ | p₂ | q₁ | q₂
      = sub just
      $ Sigma.comma-eq refl
      $ trans (Category.arrow-eq D p₁ q₁ (Functor.map F₁ f))
      $ trans (FunctorEqual.map p f)
      $ sym (Category.arrow-eq D p₂ q₂ (Functor.map F₂ f))
    
    map
      : {xs ys : SetoidCategory.Object (setoid-category-list C)}
      → (fs : SetoidCategory.Arrow (setoid-category-list C) xs ys)
      → SetoidCategory.ArrowEqual' (setoid-category-list D)
        (SetoidFunctor.map (setoid-functor-list F₁) fs)
        (SetoidFunctor.map (setoid-functor-list F₂) fs)
    map {xs = any xs} {ys = any ys} fs
      = setoid-category-list-arrow-equal' D (base' xs) (base' ys) (map' fs)

  setoid-functor-equal-list
    : FunctorEqual F₁ F₂
    → SetoidFunctorEqual
      (setoid-functor-list F₁)
      (setoid-functor-list F₂)
  setoid-functor-equal-list p
    = record {SetoidFunctorEqualList p}

-- ## SetoidFunctorIdentity

setoid-functor-identity-list
  : {C : Category}
  → {F : Functor C C}
  → FunctorIdentity F
  → SetoidFunctorIdentity
    (setoid-functor-list F)
setoid-functor-identity-list {C = C} p
  = setoid-functor-identity-from-equal
  $ setoid-functor-trans (setoid-functor-equal-list
    (functor-identity-to-equal p))
  $ setoid-functor-list-identity C

-- ## SetoidFunctorCompose

setoid-functor-compose-list
  : {C D E : Category}
  → {F : Functor D E}
  → {G : Functor C D}
  → {H : Functor C E}
  → FunctorCompose F G H
  → SetoidFunctorCompose
    (setoid-functor-list F)
    (setoid-functor-list G)
    (setoid-functor-list H)
setoid-functor-compose-list {F = F} {G = G} p
  = setoid-functor-compose-from-equal
    (setoid-functor-list F)
    (setoid-functor-list G)
  $ setoid-functor-trans (setoid-functor-equal-list
    (functor-compose-to-equal p))
  $ setoid-functor-list-compose F G

-- ## SetoidFunctorSquare

setoid-functor-square-list
  : {C₁ C₂ D₁ D₂ : Category}
  → {F : Functor C₁ C₂}
  → {G : Functor D₁ D₂}
  → {H₁ : Functor C₁ D₁}
  → {H₂ : Functor C₂ D₂}
  → FunctorSquare F G H₁ H₂
  → SetoidFunctorSquare
    (setoid-functor-list F)
    (setoid-functor-list G)
    (setoid-functor-list H₁)
    (setoid-functor-list H₂)
setoid-functor-square-list {F = F} {G = G} {H₁ = H₁} {H₂ = H₂} s
  = setoid-functor-square-from-equal
    (setoid-functor-list F)
    (setoid-functor-list G)
    (setoid-functor-list H₁)
    (setoid-functor-list H₂)
  $ setoid-functor-trans (setoid-functor-sym
    (setoid-functor-list-compose H₂ F))
  $ setoid-functor-trans (setoid-functor-equal-list
    (functor-square-to-equal s))
  $ setoid-functor-list-compose G H₁

