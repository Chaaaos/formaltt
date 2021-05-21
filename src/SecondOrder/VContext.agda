open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

module SecondOrder.VContext {ℓ} (sort : Set ℓ)  where

  -- a context is a binary tree whose leaves are labeled with sorts
  data VContext : Set ℓ where
    ctx-empty : VContext
    ctx-slot : sort → VContext
    _,,_ : VContext → VContext → VContext

  infixl 5 _,,_

  infix 4 _∈_

  -- the variables of a given type in a context
  data _∈_ (A : sort) : VContext → Set ℓ where
    var-slot : A ∈ ctx-slot A
    var-inl : ∀ {Γ Δ} (x : A ∈ Γ) → A ∈ Γ ,, Δ
    var-inr : ∀ {Γ Δ} (y : A ∈ Δ) → A ∈ Γ ,, Δ
