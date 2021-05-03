import Relation.Binary.Reasoning.Setoid as SetoidR
open import SingleSorted.AlgebraicTheory

import SingleSorted.Interpretation as Interpretation
import SingleSorted.Model as Model
import SingleSorted.UniversalInterpretation as UniversalInterpretation
import SingleSorted.Substitution as Substitution
import SingleSorted.SyntacticCategory as SyntacticCategory

module SingleSorted.UniversalModel
  {ℓt}
  {Σ : Signature}
  (T : Theory ℓt Σ) where

  open Theory T
  open Substitution T
  open UniversalInterpretation T
  open Interpretation.Interpretation ℐ
  open SyntacticCategory T

  𝒰 : Model.Model T cartesian-𝒮 ℐ
  𝒰 =
     record
        { model-eq = λ ε var-var →
                       let open SetoidR (eq-setoid (ax-ctx ε)) in
                         begin
                         interp-term (ax-lhs ε) var-var ≈⟨ interp-term-self (ax-lhs ε) var-var ⟩
                         ax-lhs ε ≈⟨ id-action ⟩
                         ax-lhs ε [ id-s ]s ≈⟨ eq-axiom ε id-s ⟩
                         ax-rhs ε [ id-s ]s ≈˘⟨ id-action ⟩
                         ax-rhs ε ≈˘⟨ interp-term-self (ax-rhs ε) var-var ⟩
                         interp-term (ax-rhs ε) var-var ∎ }
