{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Agda.Builtin.Nat using (Nat; _+_; zero; suc)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin hiding (_+_)
open import Data.Sum.Base

open import SingleSorted.AlgebraicTheory
open import SingleSorted.Interpretation using (Interpretation; TrivialI)


module SingleSorted.FactsFinite {ℓt} {Σ : Signature} (T : Theory ℓt Σ) where

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
  pre-proj₁ {Δ = suc Δ} {x = zero} = trans (cong (map suc (λ x → x)) pre-proj₁) refl
  pre-proj₁ {Δ = suc Δ} {x = suc x} = trans (cong (map suc (λ x → x)) pre-proj₁) refl

  proj₁ : ∀ {Γ Δ A : Context} {x : Fin Γ} {h : substitution Σ A Γ} {i : substitution Σ A Δ} → [ i , h ] (splitAt Δ (raise Δ x)) ≡ h x
  proj₁{Γ} {Δ} {A} {x} {h} {i} = trans (cong ([ i , h ]) pre-proj₁) refl

  pre-proj₂ : ∀ {Γ Δ : Nat} {x : Fin Δ} → ((splitAt Δ (inject+ Γ x)) ≡ inj₁ x)
  pre-proj₂ {Δ = suc Δ} {zero} = refl
  pre-proj₂ {Γ = Γ} {Δ = suc Δ} {suc x} = trans (cong (map suc (λ x₁ → x₁)) pre-proj₂) refl

  proj₂ : ∀ {Γ Δ A : Context} {x : Fin Δ} {h : substitution Σ A Γ} {i : substitution Σ A Δ} → [ i , h ] (splitAt Δ (inject+ Γ x)) ≡ i x
  proj₂{Γ} {Δ} {A} {x} {h} {i} = trans (cong ([ i , h ]) pre-proj₂) refl
