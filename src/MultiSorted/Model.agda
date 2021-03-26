open import Agda.Primitive using (_⊔_)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian
import MultiSorted.Interpretation as Interpretation

open import MultiSorted.AlgebraicTheory
open import MultiSorted.Substitution
import MultiSorted.Product as Product

module MultiSorted.Model {o ℓ e ℓt}
          {Σ : Signature}
          (T : Theory ℓt Σ)
          {𝒞 : Category.Category o ℓ e}
          (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where

  -- open Signature Σ

  -- Model of a theory

  record Model (I : Interpretation.Interpretation Σ cartesian-𝒞) : Set (ℓt ⊔ o ⊔ ℓ ⊔ e) where

    open Theory T
    open Category.Category 𝒞
    open Interpretation.Interpretation I
    open HomReasoning

    field
      model-eq : ∀ (ε : ax) → ⊨ ax-eq (ε)

    -- Soundness of semantics
    module _ where
      open Product.Producted interp-ctx

      -- first we show that substitution preserves validity
      model-resp-[]s : ∀ {Γ Δ} {A} {u v : Term Γ A} {σ : Δ ⇒s Γ} →
                       interp-term u ≈ interp-term v → interp-term (u [ σ ]s) ≈ interp-term (v [ σ ]s)
      model-resp-[]s {u = u} {v = v} {σ = σ} ξ =
        begin
          interp-term (u [ σ ]s) ≈⟨  interp-[]s {t = u} ⟩
          (interp-term u ∘ interp-subst σ)  ≈⟨ ξ ⟩∘⟨refl ⟩
          (interp-term v ∘ interp-subst σ) ≈˘⟨ interp-[]s {t = v} ⟩
          interp-term (v [ σ ]s) ∎

      -- the soundness statement
      model-⊢-≈ : ∀ {ε : Equation Σ} → ⊢ ε → ⊨ ε
      model-⊢-≈ eq-refl =  Equiv.refl
      model-⊢-≈ (eq-symm ξ) = ⟺ (model-⊢-≈ ξ)
      model-⊢-≈ (eq-tran ξ θ) = (model-⊢-≈ ξ) ○ (model-⊢-≈ θ)
      model-⊢-≈ (eq-congr ξ) = ∘-resp-≈ʳ (unique λ i → project ○ ⟺ (model-⊢-≈ (ξ i)) )
      model-⊢-≈ (eq-axiom ε σ) = model-resp-[]s {u = ax-lhs ε} {v = ax-rhs ε} (model-eq ε)

  -- Every theory has the trivial model, whose carrier is the terminal object
  Trivial : Model (Interpretation.Trivial Σ cartesian-𝒞)
  Trivial =
    let open Cartesian.Cartesian cartesian-𝒞 in
    record { model-eq = λ ε → !-unique₂ }
