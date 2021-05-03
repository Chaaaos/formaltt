open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Sum

import SingleSorted.AlgebraicTheory as SS

module SingleSorted.Combinators where


module Sum {𝓈} (Σ₁ Σ₂ : SS.Signature) (T₁ : SS.Theory 𝓈 Σ₁) (T₂ : SS.Theory 𝓈 Σ₂) where

  -- disjoint sum of signatures
  S : SS.Signature
  S = record { oper = SS.Signature.oper Σ₁  ⊎  SS.Signature.oper Σ₂
             ; oper-arity = [ SS.Signature.oper-arity Σ₁ , SS.Signature.oper-arity Σ₂ ]
             }

  inj-term-l : ∀ {Γ : SS.Context} →  SS.Signature.Term Σ₁ Γ → SS.Signature.Term S Γ
  inj-term-l {Γ} (SS.Signature.tm-var x) = SS.Signature.tm-var x
  inj-term-l {Γ} (SS.Signature.tm-oper f ts) = SS.Signature.tm-oper (inj₁ f) λ{ i → inj-term-l (ts i)}

  inj-term-r : ∀ {Γ : SS.Context} →  SS.Signature.Term Σ₂ Γ → SS.Signature.Term S Γ
  inj-term-r {Γ} (SS.Signature.tm-var x) = SS.Signature.tm-var x
  inj-term-r {Γ} (SS.Signature.tm-oper f ts) = SS.Signature.tm-oper (inj₂ f) λ{ i → inj-term-r (ts i)}

  coerce₁ : SS.Signature.Equation Σ₁ → SS.Signature.Equation S
  coerce₁ eq = record { eq-ctx = SS.Signature.Equation.eq-ctx eq
                      ; eq-lhs = inj-term-l (SS.Signature.Equation.eq-lhs eq)
                      ; eq-rhs = inj-term-l (SS.Signature.Equation.eq-rhs eq)
                      }

  coerce₂ : SS.Signature.Equation Σ₂ → SS.Signature.Equation S
  coerce₂ eq = record { eq-ctx = SS.Signature.Equation.eq-ctx eq
                      ; eq-lhs = inj-term-r (SS.Signature.Equation.eq-lhs eq)
                      ; eq-rhs = inj-term-r (SS.Signature.Equation.eq-rhs eq)
                      }

  -- define a theory with the set of axioms a union of the axioms of both theories
  T : SS.Theory 𝓈 S
  T = record { ax = SS.Theory.ax T₁ ⊎ SS.Theory.ax T₂
             ; ax-eq = [ (λ a → coerce₁ (SS.Theory.ax-eq T₁ a)) , (λ a → coerce₂ (SS.Theory.ax-eq T₂ a)) ]
             }
