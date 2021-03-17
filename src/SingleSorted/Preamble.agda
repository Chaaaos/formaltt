open import SingleSorted.AlgebraicTheory

module SingleSorted.Preamble {ℓt} {Σ : Signature} (T : Theory ℓt Σ) where

  open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
  open import Agda.Builtin.Equality
  open import Function.Base
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong-app; trans) renaming (sym to symm)
  open Eq.≡-Reasoning

  open Signature Σ
  open Theory T

  postulate
    funext : ∀ {l : Level} {X : Set l} {Y : X → Set l} {f g : ∀ (x : X) → (Y x)} → (∀ (x : X) → ((f x) ≡ (g x))) → (f ≡ g)

  congr : ∀ {l : Level} {X Y : Set l} {f : ∀ (x : X) → Y} {x y : X} → (x ≡ y) → (f x ≡ f y)
  congr refl = refl

  eq-builtin-refl : ∀ {l : Level} {Γ : Context} {x : Term Γ} {y : Term Γ} → (x ≡ y) → (Γ ⊢ x ≈ y)
  eq-builtin-refl refl = eq-refl
