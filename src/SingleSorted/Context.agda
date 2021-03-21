module SingleSorted.Context where

-- An attempt to define more structured context
-- that directly support the cartesian structure

data Context : Set where
  ctx-empty : Context
  ctx-slot : Context
  ctx-concat : Context → Context → Context

-- the variables in a context
data var : Context → Set where
  var-var  : var ctx-slot
  var-inl  : ∀ {Γ Δ} → var Γ → var (ctx-concat Γ Δ)
  var-inr  : ∀ {Γ Δ} → var Δ → var (ctx-concat Γ Δ)

-- It is absurd to have a variable in the empty context
ctx-empty-absurd : ∀ {ℓ} {A : Set ℓ} → var ctx-empty → A
ctx-empty-absurd ()
