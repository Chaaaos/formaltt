import Relation.Binary.Reasoning.Setoid as SetoidR
open import SingleSorted.AlgebraicTheory

import SingleSorted.Interpretation as Interpretation
import SingleSorted.Model as Model
import SingleSorted.UniversalInterpretation as UniversalInterpretation
import SingleSorted.Substitution as Substitution

module SingleSorted.UniversalModel
  {ℓt}
  {Σ : Signature}
  (T : Theory ℓt Σ) where

  open Theory T
  open Substitution T
  open UniversalInterpretation T
  open Interpretation.Interpretation ℐ

  𝒰 : Model.Model T ℐ
  𝒰 =
     record
        { model-eq =
            λ ε var-var →
              let open SetoidR (eq-setoid (eq-ctx ε)) in
                begin
                interp-term (eq-lhs ε) var-var   ≈⟨ interp-term-self (eq-lhs ε) var-var ⟩
                eq-lhs ε                         ≈⟨ id-action ⟩
                eq-lhs ε [ id-substitution ]s    ≈⟨ eq-axiom ε id-substitution ⟩
                eq-rhs ε [ id-substitution ]s    ≈˘⟨  id-action ⟩
                eq-rhs ε                         ≈˘⟨ interp-term-self (eq-rhs ε) var-var ⟩
                interp-term (eq-rhs ε) var-var   ∎ }
