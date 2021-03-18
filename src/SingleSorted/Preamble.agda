module SingleSorted.Preamble where

  open import Agda.Builtin.Equality

  postulate
    funext : ∀ {l} {X : Set l} {Y : X → Set l} {f g : ∀ (x : X) → (Y x)} → (∀ (x : X) → ((f x) ≡ (g x))) → (f ≡ g)
