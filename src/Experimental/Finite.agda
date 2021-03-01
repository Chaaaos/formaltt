module Experimental.Finite where

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

data Fin : ℕ → Set where
  Fin-S : ∀ {n} → Fin n → Fin (S n)
  Fin-Z : ∀ {n} → Fin (S n)
