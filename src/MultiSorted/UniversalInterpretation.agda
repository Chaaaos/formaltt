{-# OPTIONS --allow-unsolved-metas #-}

open import MultiSorted.AlgebraicTheory

import MultiSorted.Interpretation as Interpretation
import MultiSorted.SyntacticCategory as SyntacticCategory
import MultiSorted.Substitution as Substitution
import Agda.Builtin.Equality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_; refl ; cong)


module MultiSorted.UniversalInterpretation
  {ℓt}
  {Σ : Signature}
  (T : Theory ℓt Σ) where

  open Theory T
  open Substitution T
  open SyntacticCategory T

  -- The universal interpretation in the syntactic category
  interp-oper-𝒮 : ∀ (f : oper) → (prod-𝒮 (oper-arity f)) ⇒s (ctx-slot (oper-sort f))
  interp-oper-𝒮 f _ = tm-oper f λ i → tm-var i

  ℐ : Interpretation.Interpretation Σ cartesian-𝒮
  ℐ =
    record
     { interp-sort = ctx-slot
     ; interp-ctx = producted-𝒮
     ; interp-oper = interp-oper-𝒮
     }

  open Interpretation.Interpretation ℐ

  interp-term-self : ∀ {Γ} {A} (t : Term Γ A) (y : var (interp-sort A)) → ⊢ Γ ∥ (interp-term t y) ≈ t ⦂ A
  interp-term-self (tm-var x) _ = eq-refl
  interp-term-self (tm-oper f xs) _ =  eq-congr (λ i → interp-term-self (xs i) var-var)
