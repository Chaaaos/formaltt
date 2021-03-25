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
  interp-oper-𝒮 f var-var = tm-oper f λ i → tm-var i

  ℐ : Interpretation.Interpretation Σ cartesian-𝒮
  ℐ =
    record
     { interp-sort = ctx-slot
     ; interp-ctx = producted-𝒮
     ; interp-oper = interp-oper-𝒮
     }

  open Interpretation.Interpretation ℐ

  -- A term is essentially interpreted by itself
  sort-singleton-context : ∀ {Γ} {A} {y : var (ctx-slot A)} → Term Γ (sort-of (ctx-slot A) y) → Term Γ A
  sort-singleton-context {y = var-var} (tm-var x) = tm-var x
  sort-singleton-context {y = var-var} (tm-oper f x) = tm-oper f x

  ≡-sort-singleton-context : ∀ {Γ} {A} {t : Term Γ A} → interp-term {Γ = Γ} t var-var ≡ sort-singleton-context {y = var-var} (interp-term {Γ = Γ} t var-var)
  ≡-sort-singleton-context {t = Signature.tm-var x} = refl
  ≡-sort-singleton-context {t = Signature.tm-oper f x} = refl

  interp-term-self : ∀ {Γ} {A} (t : Term Γ A) (y : var (interp-sort A)) → Γ ⊢ sort-singleton-context {y = y} (interp-term t y) ≈ t ⦂ A
  interp-term-self (tm-var x)  (var-var) = eq-refl
  interp-term-self (tm-oper f xs)  (var-var) =  eq-congr λ i → eq-tran (≡-⊢-≈ (≡-sort-singleton-context {t = xs i})) (interp-term-self (xs i) var-var) -- eq-congr (λ i → interp-term-self (xs i) var-var)

  -- The names are too long, I have to find better ones...
  -- Also, I am not sure that this "sort-singleton-context" is the best way to deal with this (it doesn't seem very clean), but the fact that sort-of (ctx-slot A) y != A makes it difficult to even formulate the property "interp-term-self"
