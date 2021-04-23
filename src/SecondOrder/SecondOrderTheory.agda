open import Agda.Primitive using (lzero; lsuc; _⊔_; Level)
open import Relation.Unary hiding (_∈_)
open import Data.Empty.Polymorphic
open import Data.List
open import Function.Base
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import SecondOrder.Arity

import SecondOrder.Substitution
import SecondOrder.SecondOrderSignature as SecondOrderSignature

module SecondOrder.SecondOrderTheory {ℓs ℓo ℓa : Level} {𝔸 : Arity} {Σ : SecondOrderSignature.Signature {ℓs} {ℓo} {ℓa} 𝔸}where

    open SecondOrder.Substitution
    open SecondOrderSignature {ℓs} {ℓo} {ℓa}
    open Signature 𝔸 Σ

  -- Axioms

    record Axiom : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
      constructor make-ax
      field
        ax-mv-ctx : MetaContext -- metavariable context of an equation
        ax-sort : sort -- sort of an equation
        ax-lhs : Term ax-mv-ctx ctx-empty ax-sort -- left-hand side
        ax-rhs : Term ax-mv-ctx ctx-empty ax-sort -- right-hand side


  -- Equations

    --  equations are based on the jugements in "A general definition of dependent type theories"
    record Equation : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
      constructor make-eq
      field
        eq-mv-ctx : MetaContext -- metavariable context of an equation
        eq-ctx : Context -- variable context of an equation
        eq-sort : sort -- sort of an equation
        eq-lhs : Term eq-mv-ctx eq-ctx eq-sort -- left-hand side
        eq-rhs : Term eq-mv-ctx eq-ctx eq-sort -- right-hand side
    infix 5 make-eq
    syntax make-eq Θ Γ A s t = Θ ⊕ Γ ∥ s ≈ t ⦂ A

  -- Theory
    -- an equational theory is a family of axioms over a given sort
    record Theory ℓ : Set (lsuc (ℓ ⊔ ℓs ⊔ ℓo ⊔ ℓa)) where
      field
        ax : Set ℓ -- the axioms
        ax-eq : ax → Axiom

      ax-mv-ctx : ax → MetaContext
      ax-mv-ctx ε = Axiom.ax-mv-ctx (ax-eq ε)

      ax-sort : ax → sort
      ax-sort ε = Axiom.ax-sort (ax-eq ε)

      ax-lhs : ∀ (ε : ax) → Term (ax-mv-ctx ε) ctx-empty (ax-sort ε)
      ax-lhs ε = Axiom.ax-lhs (ax-eq ε)

      ax-rhs : ∀ (ε : ax) → Term (ax-mv-ctx ε) ctx-empty (ax-sort ε)
      ax-rhs ε = Axiom.ax-rhs (ax-eq ε)


    -- Equality of terms

      -- proof that an equation holds
      infix 4 ⊢_
      data ⊢_ : Equation → Set (lsuc (ℓ ⊔ ℓs ⊔ ℓo ⊔ ℓa)) where
        -- general rules
        eq-refl : ∀ {Θ Γ A} {t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ t ≈ t ⦂ A
        eq-symm : ∀ {Θ Γ A} {s t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Γ ∥ t ≈ s ⦂ A
        eq-trans : ∀ {Θ Γ A} {s t u : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Γ ∥ t ≈ u ⦂ A → ⊢ Θ ⊕ Γ ∥ s ≈ u ⦂ A
        -- congruence rule for operations
        eq-congr : ∀ {Γ Θ} {f : oper} {xs ys : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i)} →
                 (∀ i → ⊢ Θ ⊕ (Γ ,, arg-bind f i) ∥ (xs i) ≈ (ys i) ⦂ (arg-sort f i)) → ⊢ Θ ⊕ Γ ∥  (tm-oper f xs) ≈ (tm-oper f ys) ⦂ (oper-sort f)
        -- congruence rule for metavariables
        eq-congr-mv : ∀ {Γ Θ} {M : mv Θ} {xs ys : ∀ {B : sort} (i : mv-arg Θ M B) → Term Θ Γ B} →
                 (∀ {B : sort} (i : mv-arg Θ M B) → ⊢ Θ ⊕ Γ ∥ (xs i) ≈ (ys i) ⦂ B) → ⊢ Θ ⊕ Γ ∥  (tm-meta M xs) ≈ (tm-meta M ys) ⦂ (mv-sort Θ M)
        -- equational axiom
        eq-axiom : ∀ (ε : ax) {Θ : MetaContext} {Γ : Context} (ι : mv-inst (ax-mv-ctx ε) Θ Γ) →
                   ⊢ Θ ⊕ Γ ∥ (tm-rename (rename-ctx-empty-r {Θ = Θ}) (ax-lhs ε [ ι ]M)) ≈
                             (tm-rename (rename-ctx-empty-r {Θ = Θ}) (ax-rhs ε [ ι ]M)) ⦂ (ax-sort ε)


      _≈s_ : ∀ {Γ Δ : Context} {Θ} (σ τ : Δ ⇒s Γ) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa ⊔ ℓ))
      _≈s_ {Γ} {Δ} {Θ} σ τ = ∀ {A} (x : A ∈ Γ) → ⊢ Θ ⊕ Δ ∥ σ x ≈ τ x ⦂ A
