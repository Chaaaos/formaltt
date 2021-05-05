module SecondOrder.Context {ℓ} (Sort : Set ℓ)  where

  -- A context is a binary tree whose leaves are labeled with sorts
  data Context : Set ℓ where
    ctx-empty : Context
    ctx-slot : Sort → Context
    _,,_ : Context → Context → Context

  infixl 5 _,,_

  infix 4 _∈_

  -- the variables of a given type in a context
  data _∈_ (A : Sort) : Context → Set ℓ where
    var-slot : A ∈ ctx-slot A
    var-inl : ∀ {Γ Δ} (x : A ∈ Γ) → A ∈ Γ ,, Δ
    var-inr : ∀ {Γ Δ} (y : A ∈ Δ) → A ∈ Γ ,, Δ

  -- It is absurd to have a variable in the empty context
  ctx-empty-absurd : ∀ {ℓ} {A} {P : A ∈ ctx-empty → Set ℓ} (x : A ∈ ctx-empty) → P x
  ctx-empty-absurd ()
