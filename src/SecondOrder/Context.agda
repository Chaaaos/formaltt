module SecondOrder.Context {s} (Sort : Set s)  where

-- Contexts are binary trees which are either empty or have Sorts as leaves
data Context : Set s where
  ctx-empty : Context
  ctx-slot : Sort → Context
  _,,_ : Context → Context → Context
-- I don't know it it is a good idea, but I replaced the last constructor "ctx-concat" by "_,,_"
-- so as to make the rest of the code easier to read

infixl 5 _,,_

-- _,,_ : Context → Context → Context
-- _,,_ = ctx-concat

infix 4 _∈_

-- the variables of a given type in a context
data _∈_ (A : Sort) : Context → Set s where
  var-slot : A ∈ ctx-slot A
  var-inl : ∀ {Γ Δ} (x : A ∈ Γ) → A ∈ Γ ,, Δ
  var-inr : ∀ {Γ Δ} (y : A ∈ Δ) → A ∈ Γ ,, Δ

-- It is absurd to have a variable in the empty context
ctx-empty-absurd : ∀ {ℓ} {A} {P : A ∈ ctx-empty → Set ℓ} (x : A ∈ ctx-empty) → P x
ctx-empty-absurd ()

