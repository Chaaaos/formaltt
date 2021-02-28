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
      tm-op : Set
      ty-ty-arg : ty-op → Set
      -- ty-tm-arg : ty-op → Set
      -- tm-ty-arg : tm-op → Set
      tm-tm-arg : tm-op → Set

  open Signature

  data Theory : Set₁
  thy-signature : Theory → Signature
  data Ty (T : Theory) : Set
  data Tm (T : Theory) (A : Ty T) : Set

  data Theory where
    thy-empty : Theory
    th-type : ∀ (T : Theory) → (α : Set) → (α → Ty T) → Theory
    th-term : ∀ (T : Theory) → (α : Set) → (α → Ty T) → Ty T → Theory

  thy-signature thy-empty =
    record { ty-op = 𝟘
           ; tm-op = 𝟘
           ; ty-ty-arg = absurd
           ; tm-tm-arg = absurd
           }

  thy-signature (th-type T α x) =
    record { ty-op = (ty-op Σ) ⁺
           ; tm-op = tm-op Σ
           ; ty-ty-arg = t
           ; tm-tm-arg = tm-tm-arg Σ
           }
    where
      Σ = thy-signature T
      t : ∀ (f : (ty-op Σ) ⁺) → Set
      t Z = α
      t (S f) = ty-ty-arg (thy-signature T) f

  thy-signature (th-term T α ts t) =
    record { ty-op = ty-op Σ
           ; tm-op = (tm-op Σ) ⁺
           ; ty-ty-arg = ty-ty-arg Σ
           ; tm-tm-arg = tm
           }
    where
      Σ = thy-signature T
      tm : ∀ (f : (tm-op Σ) ⁺) → Set
      tm Z = {!!}
      tm (S x) = {!!}

  data Ty T where
    ty-expr : ∀ (f : ty-op (thy-signature T)) → (ty-ty-arg (thy-signature T) f → Ty T) → Ty T

  data Tm T A where
