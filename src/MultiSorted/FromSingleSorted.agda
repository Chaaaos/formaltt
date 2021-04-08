open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
  
open import Relation.Binary

import MultiSorted.Context as MSC
import MultiSorted.AlgebraicTheory as MST
import SingleSorted.AlgebraicTheory

module MultiSorted.FromSingleSorted
  (Σ : SingleSorted.AlgebraicTheory.Signature)
  (𝒯 : SingleSorted.AlgebraicTheory.Theory lzero Σ)
  where

module SS where
  open SingleSorted.AlgebraicTheory public
  open SingleSorted.AlgebraicTheory.Signature Σ public

data 𝒜 : Set where
  A : 𝒜

single-sort : ∀ (X : 𝒜) → X ≡ A
single-sort A = refl


-- We have to transform the following constructions from the single sorted to the multi sorted setting
-- contexts, variables, operations, terms, equations, theory


singleSortedToMultiSortedContext : ∀ {𝓈} {Sort : Set 𝓈} (X : Sort) → SS.Context → MSC.Context Sort
singleSortedToMultiSortedContext _ SS.ctx-empty = MSC.Context.ctx-empty
singleSortedToMultiSortedContext X SS.ctx-slot = MSC.Context.ctx-slot X
singleSortedToMultiSortedContext X (SS.ctx-concat Γ Δ) =
  MSC.Context.ctx-concat (singleSortedToMultiSortedContext X Γ) (singleSortedToMultiSortedContext X Δ)

multiSortedToSingleSortedContext : ∀ {𝓈} {Sort : Set 𝓈} (X : Sort) → MSC.Context Sort → SS.Context
multiSortedToSingleSortedContext X MSC.ctx-empty = SS.ctx-empty
multiSortedToSingleSortedContext X (MSC.ctx-slot x) = SS.ctx-slot
multiSortedToSingleSortedContext X (MSC.ctx-concat Γ Δ) = 
  SS.ctx-concat (multiSortedToSingleSortedContext X Γ) (multiSortedToSingleSortedContext X Δ)


S : MST.Signature 
S = record { sort = 𝒜
           ; oper = SS.Signature.oper Σ
           ; oper-arity = λ{ f → singleSortedToMultiSortedContext A (SS.Signature.oper-arity Σ f) }
           ; oper-sort = λ{ f → A }
           }

module MS where
  open MST.Signature S public


singleSortedToMultiSortedVar : ∀ {Γ : SS.Context}
  → SS.var Γ  → MS.var (singleSortedToMultiSortedContext A Γ)
singleSortedToMultiSortedVar SS.var-var = MS.var-var
singleSortedToMultiSortedVar (SS.var-inl x) = MS.var-inl (singleSortedToMultiSortedVar x)
singleSortedToMultiSortedVar (SS.var-inr x) = MS.var-inr (singleSortedToMultiSortedVar x)


-- single-sort-of : ∀ {Γ : SS.Context} {x}
--   → MS.sort-of (singleSortedToMultiSortedContext A Γ) x ≡ A
-- single-sort-of {Γ} {x} = single-sort (MSC.sort-of 𝒜 (singleSortedToMultiSortedContext A Γ) x)

coerce : ∀ {Γ : MS.Context} {X} {Y} → MS.Term Γ X → MS.Term Γ Y
coerce {Γ} {A} {A} t = subst (MS.Term Γ) refl t

argToArg : ∀ {Δ : SS.Context} → MS.arg (singleSortedToMultiSortedContext A Δ) → SS.arg Δ
argToArg {SS.ctx-slot} i = SS.var-var
argToArg {SS.ctx-concat Δ Γ} (MSC.var-inl i) = SS.var-inl (argToArg i)
argToArg {SS.ctx-concat Δ Γ} (MSC.var-inr i) = SS.var-inr (argToArg i)

singleSortedToMultiSortedTerm : ∀ {Γ : SS.Context}
  → SS.Term Γ
  → MS.Term (singleSortedToMultiSortedContext A Γ) A
singleSortedToMultiSortedTerm {Γ} (SS.tm-var x) = coerce (MS.tm-var (singleSortedToMultiSortedVar x))
singleSortedToMultiSortedTerm (SS.tm-oper f ts) = MS.tm-oper f
  (λ i → coerce (singleSortedToMultiSortedTerm (ts (argToArg i))))

singleSortedToMultiSortedEquation : SS.Equation → MST.Equation S
singleSortedToMultiSortedEquation eq = 
  MST.make-eq
    (singleSortedToMultiSortedContext A (SS.Equation.eq-ctx eq))
    A
    (singleSortedToMultiSortedTerm (SS.Equation.eq-lhs eq))
    (singleSortedToMultiSortedTerm (SS.Equation.eq-rhs eq))

𝓣 : MST.Theory lzero S
𝓣 = record { ax = SS.Theory.ax 𝒯
            ; ax-eq = λ{ a → singleSortedToMultiSortedEquation (SS.Theory.ax-eq 𝒯 a)}
            }
