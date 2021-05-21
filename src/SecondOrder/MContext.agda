module SecondOrder.MContext {ℓ} (arity : Set ℓ) (sort : Set ℓ)  where

  data MContext : Set ℓ where
    ctx-empty : MContext
    ctx-slot : arity → sort → MContext
    _,,_ : MContext → MContext → MContext

  infixl 5 _,,_

  infix 4 [_,_]∈_

  -- the meta-variables of a given type in a context
  data [_,_]∈_ (Λ : arity) (A : sort) : MContext → Set ℓ where
    var-slot : [ Λ , A ]∈ ctx-slot Λ A
    var-inl : ∀ {Γ Δ} (x : [ Λ , A ]∈ Γ) → [ Λ , A ]∈ Γ ,, Δ
    var-inr : ∀ {Γ Δ} (y : [ Λ , A ]∈ Δ) → [ Λ , A ]∈ Γ ,, Δ
