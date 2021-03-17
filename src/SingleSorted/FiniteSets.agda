open import SingleSorted.AlgebraicTheory
open import SingleSorted.Interpretation using (Interpretation; TrivialI)

module SingleSorted.FiniteSets {ℓt} {Σ : Signature} (T : Theory ℓt Σ) where


  open import Agda.Builtin.Nat public --using (_+_; Nat)
  open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
  open import Agda.Builtin.Equality
  open import Data.Fin renaming (_+_ to _+ᶠ_)
  open import Function.Base
  open import Data.Sum.Base
  open import Data.Nat.Properties using (+-comm)
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong-app; trans) renaming (sym to symm)
  open Eq.≡-Reasoning

  open import Categories.Category
  open import Categories.Category.Cartesian

  open import SingleSorted.CartesianCategories public
  open import SingleSorted.Preamble public

  open Signature Σ
  open Theory T

    -- handling finite sets
  swap-Fin : ∀ {Γ Δ} → Fin (Γ + Δ) → Fin (Δ + Γ)
  swap-Fin {Γ} {Δ} = λ  x → cast (+-comm Γ Δ) x

  lift-prod₁ : ∀ {Δ Γ} → Fin Γ → Fin (Γ + Δ)
  lift-prod₁ {Δ} {Γ} a = swap-Fin {Δ} {Γ} (raise Δ a)

  lift-prod₂ : ∀ {Δ Γ} → Fin Δ → Fin (Γ + Δ)
  lift-prod₂ {Δ} {Γ} a =  swap-Fin {Δ} {Γ}(inject+ Γ a)

  pre-proj₁ : ∀ {Γ Δ : Nat}  {x : Fin Γ} → (splitAt Δ (raise Δ x)) ≡ (inj₂ x)
  pre-proj₁ {Δ = zero} = refl
  pre-proj₁ {Δ = suc Δ} {x = zero} = {!refl!}
  pre-proj₁ {Δ = suc Δ} {x = suc x} = {!!}

  proj₁ : ∀ {Γ Δ A : Context} {x : Fin Γ} {h : substitution Σ A Γ} {i : substitution Σ A Δ} → [ i , h ] (splitAt Δ (raise Δ x)) ≡ h x
  proj₁{Γ} {Δ} {A} {x} {h} {i} = trans (congr T {f = [ i , h ]} {x = (splitAt Δ (raise Δ x))} {y = inj₂ x} pre-proj₁) refl

  pre-proj₂ : ∀ {Γ Δ : Nat} {x : Fin Δ} → ((splitAt Δ (inject+ Γ x)) ≡ inj₁ x)
  pre-proj₂ = {!!}

  proj₂ : ∀ {Γ Δ A : Context} {x : Fin Δ} {h : substitution Σ A Γ} {i : substitution Σ A Δ} → [ i , h ] (splitAt Δ (inject+ Γ x)) ≡ i x
  proj₂{Γ} {Δ} {A} {x} {h} {i} = trans (congr T {f = [ i , h ]} {x = (splitAt Δ (inject+ Γ x))} {y = inj₁ x} pre-proj₂) refl
