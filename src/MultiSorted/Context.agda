module MultiSorted.Context (Sort : Set)  where

-- An attempt to define more structured context
-- that directly support the cartesian structure

data Context : Set where
  ctx-empty : Context
  ctx-slot : Sort → Context
  ctx-concat : Context → Context → Context

-- the variables in a context
data var : Context → Set where
  var-var  : ∀ {A} → var (ctx-slot A)
  var-inl  : ∀ {Γ Δ} → var Γ → var (ctx-concat Γ Δ)
  var-inr  : ∀ {Γ Δ} → var Δ → var (ctx-concat Γ Δ)

sort-of : ∀ (Γ : Context) → var Γ → Sort
sort-of (ctx-slot A) var-var = A
sort-of (ctx-concat Γ Δ) (var-inl x) = sort-of Γ x
sort-of (ctx-concat Γ Δ) (var-inr x) = sort-of Δ x

-- It is absurd to have a variable in the empty context
ctx-empty-absurd : ∀ {ℓ} {P : var ctx-empty → Set ℓ} (x : var ctx-empty) → P x
ctx-empty-absurd ()
