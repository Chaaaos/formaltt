{-# OPTIONS --allow-unsolved-metas #-}

open import MultiSorted.AlgebraicTheory

import MultiSorted.Interpretation as Interpretation
import MultiSorted.SyntacticCategory as SyntacticCategory
import MultiSorted.Substitution as Substitution


module MultiSorted.UniversalInterpretation
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
     { interp-sort = ctx-slot
     ; interp-ctx = power-𝒮
     ; interp-oper = λ f var-var → {!!} -- tm-oper f (λ i → tm-var i)
     }

  open Interpretation.Interpretation ℐ

  -- A term is essentially interpreted by itself
  interp-term-self : ∀ {Γ} {A} (t : Term Γ A) y → {!!} -- Γ ⊢ interp-term t y ≈ t ⦂ A
  interp-term-self (tm-var x) _ = eq-refl
  interp-term-self (tm-oper f xs) y = eq-congr (λ i → interp-term-self (xs i) var-var)
