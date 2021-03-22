-- This file is very likely obsolete as we do not use natural numbers and finite sets anymore

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Agda.Builtin.Nat using (Nat; _+_; zero; suc)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin hiding (_+_)
open import Data.Sum.Base
open import Data.Sum.Properties
open import Function.Base using (_∘_)

open import SingleSorted.AlgebraicTheory
open import SingleSorted.Interpretation using (Interpretation; TrivialI)


module SingleSorted.FactsFinite {ℓt} {Σ : Signature} (T : Theory ℓt Σ) where

  open Signature Σ
  open Theory T
  open import SingleSorted.Substitution {ℓt} {Σ} T

  ≡-eq-refl : ∀ {Γ : Context} {s : Term Γ} {t : Term Γ} → s ≡ t → Γ ⊢ s ≈ t
  ≡-eq-refl refl = eq-refl

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

  pre-unique :
     ∀ {Γ Δ C : Context}
       {h  : substitution Σ C (Δ + Γ)}
       {i  : substitution Σ C Γ}
       {j  : substitution Σ C Δ}
       {p₁ : (λ x → h (raise Δ x)) ≈s i}
       {p₂ : (λ y → h (inject+ Γ y)) ≈s j}
       {x  : var (Δ + Γ)}
       → C ⊢ ([ j , i ] (splitAt Δ x)) ≈ (h x)

  pre-unique {Δ = zero} {h = h} {i = i} {p₁ = p₁} {x = zero} =
    equiv-subst i h (symm-subst p₁) (tm-var zero)

  pre-unique {Δ = zero} {h = h} {i = i} {p₁ = p₁} {x = suc x} =
    equiv-subst i h (symm-subst p₁) (tm-var (suc x))

  pre-unique {Γ} {Δ = suc Δ} {h = h} {j = j} {p₂ = p₂} {x = zero} =
    equiv-subst j (h ∘ inject+ Γ) (symm-subst p₂) (tm-var zero)

  pre-unique {Δ = suc Δ} {C = C} {h = h} {i} {j} {p₁} {p₂} {x = suc x} =
    eq-tran
      (≡-eq-refl ([,]-map-commute (splitAt Δ x)))
      (pre-unique
         {Δ = Δ}
         {h = h ∘ suc}
         {i}
         {j = j ∘ suc}
         {p₁}
         {p₂ = p₂ ∘ suc}
         {x = x})
