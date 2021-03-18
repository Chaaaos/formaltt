{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (_⊔_)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

import SingleSorted.Interpretation as Interpretation
import SingleSorted.FactsCartesian as FactsCartesian

open import SingleSorted.AlgebraicTheory

module SingleSorted.Model {o ℓ e ℓt}
          {Σ : Signature}
          (T : Theory ℓt Σ)
          {𝒞 : Category.Category o ℓ e}
          {cartesian-𝒞 : Cartesian.Cartesian 𝒞} where

  open Signature Σ
  open Theory T

  -- Model of a theory

  record Model (I : Interpretation.Interpretation Σ cartesian-𝒞)  : Set (ℓt ⊔ o ⊔ ℓ ⊔ e) where

    open Interpretation.Interpretation I
    open Category.Category 𝒞

    field
      model-eq : ∀ (ε : eq) → interp-term (eq-lhs ε) ≈ interp-term (eq-rhs ε)

  -- Every theory has the trivial model, whose carrier is the terminal object
  TrivialM : Model (Interpretation.TrivialI Σ cartesian-𝒞)
  TrivialM =
     let open Cartesian.Cartesian cartesian-𝒞 in
     record { model-eq = λ ε → !-unique₂ }
