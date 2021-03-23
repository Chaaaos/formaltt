module MultiSorted.Context (Sort : Set)  where


-- An attempt to define more structured context
-- that directly support the cartesian structure

data Context : Set where
  ctx-empty : Context
  ctx-slot : Context
  ctx-concat : Context → Context → Context

-- the variables in a context
data var (A : Sort) : Context → Set where
  var-var  : var A ctx-slot
  var-inl  : ∀ {Γ Δ} → var A Γ → var A (ctx-concat Γ Δ)
  var-inr  : ∀ {Γ Δ} → var A Δ → var A (ctx-concat Γ Δ)

-- It is absurd to have a variable in the empty context
ctx-empty-absurd : ∀ {ℓ} {B : Set ℓ} {A : Sort} → var A ctx-empty → B
ctx-empty-absurd ()
