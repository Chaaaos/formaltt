import Relation.Binary.Reasoning.Setoid as SetoidR
open import MultiSorted.AlgebraicTheory

import MultiSorted.Interpretation as Interpretation
import MultiSorted.Model as Model
import MultiSorted.UniversalInterpretation as UniversalInterpretation
import MultiSorted.Substitution as Substitution
import MultiSorted.SyntacticCategory as SyntacticCategory

module MultiSorted.UniversalModel
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
                       let open SetoidR (eq-setoid (eq-ctx ε) (sort-of (ctx-slot (eq-sort ε)) var-var)) in
                       begin
                       Interpretation.Interpretation.interp-term ℐ (eq-lhs ε) var-var ≈⟨ ≡-⊢-≈ (≡-sort-singleton-context) ⟩
                       {!!}
                             }

 -- sort-singleton-context (interp-term (eq-lhs ε) var-var) ≈⟨ interp-term-self (eq-lhs ε) var-var ⟩
 --                         eq-lhs ε ≈⟨ id-action ⟩
 --                         eq-lhs ε [ id-s ]s ≈⟨ eq-axiom ε id-s ⟩
 --                         eq-rhs ε [ id-s ]s ≈˘⟨ id-action ⟩
 --                         eq-rhs ε ≈˘⟨ interp-term-self (eq-rhs ε) var-var ⟩
 --                         sort-singleton-context (interp-term (eq-rhs ε) var-var) ∎
