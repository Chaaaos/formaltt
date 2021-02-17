module SimpleTT where

  data 𝟘 : Set where

  absurd : ∀ {ℓ} {A : Set ℓ} → 𝟘 → A
  absurd ()

  data _⁺ (A : Set) : Set where
     Z : A ⁺
     S : A → A ⁺

  record Signature : Set₁ where
    field
      ty-op : Set
      -- tm-op : Set
      ty-ty-arg : ty-op → Set
      -- ty-tm-arg : ty-op → Set
      -- tm-ty-arg : tm-op → Set
      -- tm-tm-arg : tm-op → Set

  open Signature

  data Theory : Set₁
  thy-signature : Theory → Signature
  data Ty (T : Theory) : Set

  data Theory where
    thy-empty : Theory
    th-type : ∀ (T : Theory) → (α : Set) → (α → Ty T) → Theory

  thy-signature thy-empty =  record { ty-op = 𝟘 ; ty-ty-arg = absurd }
  thy-signature (th-type T α x) = record { ty-op = β ; ty-ty-arg = τ }
    where
      β : Set
      β = (ty-op (thy-signature T)) ⁺
      τ : β → Set
      τ Z = α
      τ (S f) = ty-ty-arg (thy-signature T) f

  data Ty T where
    ty-expr : ∀ (f : ty-op (thy-signature T)) → (ty-ty-arg (thy-signature T) f → Ty T) → Ty T
