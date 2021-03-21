{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (_⊔_)

import Categories.Category as Category
import SingleSorted.Interpretation as Interpretation

open import SingleSorted.AlgebraicTheory
open import SingleSorted.Substitution
import SingleSorted.Power as Power

module SingleSorted.Model {o ℓ e ℓt}
          {Σ : Signature}
          (T : Theory ℓt Σ)
          {𝒞 : Category.Category o ℓ e} where

  open Signature Σ

  -- Model of a theory

  record Model (I : Interpretation.Interpretation Σ 𝒞)  : Set (ℓt ⊔ o ⊔ ℓ ⊔ e) where

    open Interpretation.Interpretation I
    open Category.Category 𝒞
    open HomReasoning
    open Theory T

    field
      model-eq : ∀ (ε : eq) → interp-term (eq-lhs ε) ≈ interp-term (eq-rhs ε)

    -- Soundness of semantics
    module _ where
      open Power.Powered interp-power

      model-⊢-≈ : ∀ {Γ} {s t : Term Γ} → Γ ⊢ s ≈ t → interp-term s ≈ interp-term t
      model-⊢-≈ eq-refl =  Equiv.refl
      model-⊢-≈ (eq-symm ξ) = ⟺ (model-⊢-≈ ξ)
      model-⊢-≈ (eq-tran ξ θ) = (model-⊢-≈ ξ) ○ (model-⊢-≈ θ)
      model-⊢-≈ (eq-congr ξ) = ∘-resp-≈ʳ (unique (λ i → project ○ model-⊢-≈ (eq-symm (ξ i))))
      model-⊢-≈ (eq-axiom ε σ) = {!!}

  -- Every theory has the trivial model, whose carrier is the terminal object
  TrivialM : Model (Interpretation.TrivialI Σ cartesian-𝒞)
  TrivialM =
     let open Power.Powered interp-power in
     record { model-eq = λ ε → ! }
