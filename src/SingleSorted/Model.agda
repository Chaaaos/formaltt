open import Agda.Primitive using (_⊔_)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian
import SingleSorted.Interpretation as Interpretation

open import SingleSorted.AlgebraicTheory
open import SingleSorted.Substitution
import SingleSorted.Power as Power

module SingleSorted.Model {o ℓ e ℓt}
          {Σ : Signature}
          (T : Theory ℓt Σ)
          {𝒞 : Category.Category o ℓ e}
          (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where

  -- Model of a theory

  record Model (I : Interpretation.Interpretation Σ cartesian-𝒞) : Set (ℓt ⊔ o ⊔ ℓ ⊔ e) where

    open Theory T
    open Category.Category 𝒞
    open Interpretation.Interpretation I
    open HomReasoning

    field
      model-eq : ∀ (ε : eq) → interp-term (eq-lhs ε) ≈ interp-term (eq-rhs ε)

    -- Soundness of semantics
    module _ where
      open Power.Powered interp-pow

      -- first we show that substitution preserves validity
      model-resp-[]s : ∀ {Γ Δ} {u v : Term Γ} {σ : substitution Δ Γ} →
                       interp-term u ≈ interp-term v → interp-term (u [ σ ]s) ≈ interp-term (v [ σ ]s)
      model-resp-[]s {u = u} {v = v} {σ = σ} ξ =
        begin
          interp-term (u [ σ ]s) ≈⟨  interp-[]s {t = u} ⟩
          (interp-term u ∘ interp-subst σ)  ≈⟨ ξ ⟩∘⟨refl ⟩
          (interp-term v ∘ interp-subst σ) ≈˘⟨ interp-[]s {t = v} ⟩
          interp-term (v [ σ ]s) ∎

      -- the soundness statement
      model-⊢-≈ : ∀ {Γ} {s t : Term Γ} → Γ ⊢ s ≈ t → interp-term s ≈ interp-term t
      model-⊢-≈ eq-refl =  Equiv.refl
      model-⊢-≈ (eq-symm ξ) = ⟺ (model-⊢-≈ ξ)
      model-⊢-≈ (eq-tran ξ θ) = (model-⊢-≈ ξ) ○ (model-⊢-≈ θ)
      model-⊢-≈ (eq-congr ξ) = ∘-resp-≈ʳ (unique (λ i → project ○ model-⊢-≈ (eq-symm (ξ i))))
      model-⊢-≈ (eq-axiom ε σ) = model-resp-[]s {u = eq-lhs ε} {v = eq-rhs ε} (model-eq ε)

  -- Every theory has the trivial model, whose carrier is the terminal object
  Trivial : Model (Interpretation.Trivial Σ cartesian-𝒞)
  Trivial =
    let open Cartesian.Cartesian cartesian-𝒞 in
    record { model-eq = λ ε → !-unique₂ }
