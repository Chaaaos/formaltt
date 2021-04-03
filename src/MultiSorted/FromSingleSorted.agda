open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Fin
-- import Data.Nat
  
open import Relation.Binary

import MultiSorted.Context as MS
open import MultiSorted.AlgebraicTheory
import SingleSorted.AlgebraicTheory as SS

module MultiSorted.FromSingleSorted
  (Σ : SS.Signature)
  (𝒯 : SS.Theory lzero Σ)
  where

open SS.Signature Σ renaming (Equation to ss-Equation; Term to ss-Term; oper to ss-oper; oper-arity to ss-oper-arity)

data 𝒜 : Set where
  A : 𝒜

single-sort : ∀ (X : 𝒜) → X ≡ A
single-sort A = refl

-- We have to transform the following constructions from the single sorted to the multi sorted setting
-- contexts, variables, operations, terms, equations, theory


singleSortedToMultiSortedContext : SS.Context → MS.Context 𝒜
singleSortedToMultiSortedContext SS.ctx-empty = MS.ctx-empty
singleSortedToMultiSortedContext SS.ctx-slot = MS.ctx-slot A
singleSortedToMultiSortedContext (SS.ctx-concat Γ Δ) =
  MS.ctx-concat (singleSortedToMultiSortedContext Γ) (singleSortedToMultiSortedContext Δ)

S : Signature
S = record { sort = 𝒜
           ; oper = ss-oper
           ; oper-arity = λ{ f → singleSortedToMultiSortedContext (ss-oper-arity f) }
           ; oper-sort = λ{ f → A }
           }

open Signature S

singleSortedToMultiSortedVar : ∀ {Γ : SS.Context} → SS.var Γ  → var (singleSortedToMultiSortedContext Γ)
singleSortedToMultiSortedVar SS.var-var = var-var {A}
singleSortedToMultiSortedVar (SS.var-inl x) = var-inl (singleSortedToMultiSortedVar x)
singleSortedToMultiSortedVar (SS.var-inr x) = var-inr (singleSortedToMultiSortedVar x)


single-sort-of : ∀ {Γ : SS.Context} {x : SS.var Γ}
  → sort-of (singleSortedToMultiSortedContext Γ) (singleSortedToMultiSortedVar x) ≡ A
single-sort-of {Γ} {x} = single-sort (MS.sort-of 𝒜 (singleSortedToMultiSortedContext Γ) (singleSortedToMultiSortedVar x))

singleSortedToMultiSortedTerm : ∀ {Γ : SS.Context}
  → ss-Term Γ
  → Term (singleSortedToMultiSortedContext Γ) A
singleSortedToMultiSortedTerm {Γ} (SS.Signature.tm-var x) rewrite (single-sort-of {Γ} {x})
  = {!tm-var (singleSortedToMultiSortedVar x)!}
singleSortedToMultiSortedTerm {Γ} (SS.Signature.tm-oper f x) = tm-oper f λ{ i → {!singleSortedToMultiSortedTerm x!}}


singleSortedToMultiSortedEquation : ss-Equation → Equation S
singleSortedToMultiSortedEquation eq =
  make-eq
    (singleSortedToMultiSortedContext (ss-Equation.eq-ctx eq))
    A
    (singleSortedToMultiSortedTerm (ss-Equation.eq-lhs eq))
    (singleSortedToMultiSortedTerm (ss-Equation.eq-rhs eq))

𝓣 : Theory lzero S
𝓣 = record { ax = SS.Theory.ax 𝒯
            ; ax-eq = λ{ a → singleSortedToMultiSortedEquation (SS.Theory.ax-eq 𝒯 a)}
            }


