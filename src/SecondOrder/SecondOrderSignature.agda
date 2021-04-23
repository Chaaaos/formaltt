open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Unary hiding (_∈_)
open import Data.Empty.Polymorphic
open import Data.List
open import Function.Base
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import SecondOrder.Arity

import SecondOrder.Context as Context

module SecondOrder.SecondOrderSignature {ℓs ℓo ℓa} (𝔸 : Arity) where


  -- Signature

  -- a second-order algebraic signature
  record Signature : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
    open Arity 𝔸

    field
      sort : Set ℓs -- sorts
      oper : Set ℓo -- operations

    open Context sort public

    field
      oper-arity : oper → arity -- the arity of an operation
      oper-sort : oper → sort -- the operation sort
      arg-sort : ∀ (f : oper) → arg (oper-arity f) → sort -- the sorts of arguments
      arg-bind : ∀ (f : oper) → arg (oper-arity f) → Context -- the argument bindings

    -- the arguments of an operation
    oper-arg : oper → Set
    oper-arg f = arg (oper-arity f)



  -- Metavariables

    -- a metavariable context
    record MetaContext : Set (lsuc ℓs) where
      field
        mv : Set ℓs -- the metavariables
        mv-arity : mv → Context -- the arity of a metavariable
        mv-sort : mv → sort -- the sort of a metavariable

    open MetaContext public

    mv-arg : ∀ (Θ : MetaContext) → mv Θ → sort → Set ℓs
    mv-arg Θ M A = A ∈ (mv-arity Θ M)


  -- Terms

    -- terms in a context of a given sort
    data Term (Θ : MetaContext) : ∀ (Γ : Context) (A : sort) → Set (lsuc (ℓa ⊔ ℓo ⊔ ℓs)) where
      tm-var : ∀ {Γ} {A} (x : A ∈ Γ) → Term Θ Γ A
      tm-meta : ∀ {Γ} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B) → Term Θ Γ (mv-sort Θ M)
      tm-oper : ∀ {Γ} (f : oper)
                  (es : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i)) →
                  Term Θ Γ (oper-sort f)
