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
    var-inl : ∀ {Θ ψ} (x : [ Λ , A ]∈ Θ) → [ Λ , A ]∈ Θ ,, ψ
    var-inr : ∀ {Θ ψ} (y : [ Λ , A ]∈ ψ) → [ Λ , A ]∈ Θ ,, ψ
