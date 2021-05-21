module SecondOrder.MContext {ℓ} (arity : Set ℓ) (sort : Set ℓ)  where

  data MContext : Set ℓ where
    ctx-empty : MContext
    ctx-slot : arity → sort → MContext
    _,,_ : MContext → MContext → MContext

  infixl 5 _,,_

  infix 4 [_,_]∈_

  -- the meta-variables of a given type in a context
  data [_,_]∈_ (α : arity) (A : sort) : MContext → Set ℓ where
    var-slot : [ α , A ]∈ ctx-slot α A
    var-inl : ∀ {Γ Δ} (x : [ α , A ]∈ Γ) → [ α , A ]∈ Γ ,, Δ
    var-inr : ∀ {Γ Δ} (y : [ α , A ]∈ Δ) → [ α , A ]∈ Γ ,, Δ
