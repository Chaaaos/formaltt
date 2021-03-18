{-# OPTIONS --allow-unsolved-metas #-}
open import SingleSorted.AlgebraicTheory
open import SingleSorted.Interpretation using (Interpretation; TrivialI)

module SingleSorted.FiniteSets {ℓt} {Σ : Signature} (T : Theory ℓt Σ) where

  open import SingleSorted.Preamble public
  open import Data.Fin renaming (_+_ to _+ᶠ_)

  open Signature Σ
  open Theory T

    -- Handling finite sets (useful to define the cartesian structure of the syntactic category)
  swap-Fin : ∀ {Γ Δ} → Fin (Γ + Δ) → Fin (Δ + Γ)
  swap-Fin {Γ} {Δ} = λ  x → cast (+-comm Γ Δ) x

  lift-prod₁ : ∀ {Δ Γ} → Fin Γ → Fin (Γ + Δ)
  lift-prod₁ {Δ} {Γ} a = swap-Fin {Δ} {Γ} (raise Δ a)

  lift-prod₂ : ∀ {Δ Γ} → Fin Δ → Fin (Γ + Δ)
  lift-prod₂ {Δ} {Γ} a =  swap-Fin {Δ} {Γ}(inject+ Γ a)

  pre-proj₁ : ∀ {Γ Δ : Nat}  {x : Fin Γ} → (splitAt Δ (raise Δ x)) ≡ (inj₂ x)
  pre-proj₁ {Δ = zero} = refl
  pre-proj₁ {Δ = suc Δ} {x = zero} = trans (congr T {f = map suc (λ x → x)} {x = splitAt Δ (raise Δ zero)} {y = inj₂ zero} pre-proj₁) refl
  pre-proj₁ {Δ = suc Δ} {x = suc x} = trans (congr T {f = map suc (λ x → x)} {x = splitAt Δ (raise Δ (suc x))} {y = inj₂ (suc x)} pre-proj₁) refl

  proj₁ : ∀ {Γ Δ A : Context} {x : Fin Γ} {h : substitution Σ A Γ} {i : substitution Σ A Δ} → [ i ⊎ h ] (splitAt Δ (raise Δ x)) ≡ h x
  proj₁{Γ} {Δ} {A} {x} {h} {i} = trans (congr T {f = [ i ⊎ h ]} {x = (splitAt Δ (raise Δ x))} {y = inj₂ x} pre-proj₁) refl

  pre-proj₂ : ∀ {Γ Δ : Nat} {x : Fin Δ} → ((splitAt Δ (inject+ Γ x)) ≡ inj₁ x)
  pre-proj₂ {Δ = suc Δ} {zero} = refl
  pre-proj₂ {Γ = Γ} {Δ = suc Δ} {suc x} = trans (congr T {f = map suc (λ x₁ → x₁)} {x = (splitAt Δ (inject+ Γ x))} {y = inj₁ x} pre-proj₂) refl

  proj₂ : ∀ {Γ Δ A : Context} {x : Fin Δ} {h : substitution Σ A Γ} {i : substitution Σ A Δ} → [ i ⊎ h ] (splitAt Δ (inject+ Γ x)) ≡ i x
  proj₂{Γ} {Δ} {A} {x} {h} {i} = trans (congr T {f = [ i ⊎ h ]} {x = (splitAt Δ (inject+ Γ x))} {y = inj₁ x} pre-proj₂) refl
