open import SingleSorted.AlgebraicTheory

import SingleSorted.Interpretation as Interpretation
import SingleSorted.SyntacticCategory as SyntacticCategory
import SingleSorted.Substitution as Substitution


module SingleSorted.UniversalInterpretation
  {ℓt}
  {Σ : Signature}
  (T : Theory ℓt Σ) where

  open Theory T
  open Substitution T
  open SyntacticCategory T

  -- The universal interpretation in the syntactic category
  ℐ : Interpretation.Interpretation Σ cartesian-𝒮
  ℐ =
    record
     { interp-carrier = ctx-slot
     ; interp-power = power-𝒮
     ; interp-oper = λ f var-var → tm-oper f (λ i → tm-var i)
     }

  open Interpretation.Interpretation ℐ

  -- A term is essentially interpreted by itself
  interp-term-self : ∀ {Γ} (t : Term Γ) y → Γ ⊢ interp-term t y ≈ t
  interp-term-self (tm-var x) _ = eq-refl
  interp-term-self (tm-oper f xs) y = eq-congr (λ i → interp-term-self (xs i) var-var)
