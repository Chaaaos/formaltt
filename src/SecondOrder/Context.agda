module SecondOrder.Context {s} (Sort : Set s)  where

data Context : Set s where
  ctx-empty : Context
  ctx-slot : Sort → Context
  ctx-concat : Context → Context → Context

infixl 5 _,,_

_,,_ : Context → Context → Context
_,,_ = ctx-concat

infix 4 _∈_

-- the variables of a given type in a context
data _∈_ (A : Sort) : Context → Set s where
  var-slot : A ∈ ctx-slot A
  var-inl : ∀ {Γ Δ} (x : A ∈ Γ) → A ∈ Γ ,, Δ
  var-inr : ∀ {Γ Δ} (y : A ∈ Δ) → A ∈ Γ ,, Δ

-- It is absurd to have a variable in the empty context
ctx-empty-absurd : ∀ {ℓ} {A} {P : A ∈ ctx-empty → Set ℓ} (x : A ∈ ctx-empty) → P x
ctx-empty-absurd ()
