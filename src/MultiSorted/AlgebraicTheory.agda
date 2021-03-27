open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin

open import Relation.Binary

import MultiSorted.Context as Context

module MultiSorted.AlgebraicTheory where

  -- an algebraic signature
  record Signature {𝓈 ℴ} : Set (lsuc (𝓈 ⊔ ℴ)) where
    field
      sort : Set 𝓈 -- sorts
      oper : Set ℴ -- operations

    open Context sort public

    -- Arity and arguments
    Arity : Set 𝓈
    Arity = Context

    field
      oper-arity : oper → Arity -- the arity of an operation (with the sorts of the arguments)
      oper-sort : oper → sort -- the sort of an operation

    arg : Arity → Set
    arg = var

    arg-sort : ∀ (f : oper) → arg (oper-arity f) → sort
    arg-sort f = sort-of (oper-arity f)

    -- terms in a context of a given sort
    data Term (Γ : Context) : ∀ (A : sort) → Set (lsuc ℴ) where
      tm-var : ∀ (x : var Γ) → Term Γ (sort-of Γ x)
      tm-oper : ∀ (f : oper) → (∀ (i : arg (oper-arity f)) → Term Γ (arg-sort f i)) → Term Γ (oper-sort f)

    -- Substitutions (definitions - some useful properties are in another file)
    _⇒s_ : ∀ (Γ Δ : Context) → Set (lsuc ℴ)
    Γ ⇒s Δ = ∀ (x : var Δ) → Term Γ (sort-of Δ x)

    infix  4 _⇒s_

    -- identity substitution
    id-s : ∀ {Γ : Context} → Γ ⇒s Γ
    id-s = tm-var

    -- the action of a substitution on a term (contravariant)
    _[_]s : ∀ {Γ Δ : Context} {A : sort} → Term Δ A → Γ ⇒s Δ → Term Γ A
    (tm-var x) [ σ ]s = σ x
    (tm-oper f ts) [ σ ]s = tm-oper f (λ i → ts i [ σ ]s)

    infixr 6 _[_]s

    -- composition of substitutions
    _∘s_ : ∀ {Γ Δ Θ : Context} → Δ ⇒s Θ → Γ ⇒s Δ → Γ ⇒s Θ
    (σ ∘s ρ) x = σ x [ ρ ]s

    infixl 7 _∘s_

  -- Equations
  record Equation {s o} (Σ : Signature {s} {o} ) : Set (lsuc (s ⊔ o)) where
    constructor make-eq
    field
      eq-ctx : Signature.Context Σ
      eq-sort : Signature.sort Σ
      eq-lhs : Signature.Term Σ eq-ctx eq-sort
      eq-rhs : Signature.Term Σ eq-ctx eq-sort

  infix 5 make-eq

  syntax make-eq Γ A s t = Γ ∥ s ≈ t ⦂ A
  -- Theory
  -- an equational theory is a family of axioms over a given sort
  record Theory ℓ {𝓈 ℴ} (Σ : Signature {𝓈} {ℴ}) : Set (lsuc (ℓ ⊔ 𝓈 ⊔ ℴ)) where
    open Signature Σ public
    field
      ax : Set ℓ -- the axioms
      ax-eq : ax → Equation Σ

    ax-ctx : ax → Context
    ax-ctx ε = Equation.eq-ctx (ax-eq ε)

    ax-sort : ax → sort
    ax-sort ε = Equation.eq-sort (ax-eq ε)

    ax-lhs : ∀ (ε : ax) → Term (ax-ctx ε) (ax-sort ε)
    ax-lhs ε = Equation.eq-lhs (ax-eq ε)

    ax-rhs : ∀ (ε : ax) → Term (ax-ctx ε) (ax-sort ε)
    ax-rhs ε = Equation.eq-rhs (ax-eq ε)

    -- equality of terms
    infix 4 ⊢_

    data ⊢_ : Equation Σ → Set (lsuc (ℓ ⊔ 𝓈 ⊔ ℴ)) where
      -- general rules
      eq-refl : ∀ {Γ A} {t : Term Γ A} → ⊢ Γ ∥ t ≈ t ⦂ A
      eq-symm : ∀ {Γ A} {s t : Term Γ A} → ⊢ Γ ∥ s ≈ t ⦂ A → ⊢ Γ ∥ t ≈ s ⦂ A
      eq-tran : ∀ {Γ A} {s t u : Term Γ A} → ⊢ Γ ∥ s ≈ t ⦂ A → ⊢ Γ ∥ t ≈ u ⦂ A → ⊢ Γ ∥ s ≈ u ⦂ A
      -- congruence rule
      eq-congr : ∀ {Γ} {f : oper} {xs ys : ∀ (i : arg (oper-arity f)) → Term Γ (sort-of (oper-arity f) i)} →
                (∀ i → ⊢ Γ ∥ (xs i) ≈ (ys i) ⦂ (sort-of (oper-arity f) i)) → ⊢ Γ ∥  (tm-oper f xs) ≈ (tm-oper f ys) ⦂ (oper-sort f)
      -- equational axiom
      eq-axiom : ∀ (ε : ax) {Γ : Context} (σ : Γ ⇒s ax-ctx ε) →
                 ⊢ Γ ∥ (ax-lhs ε [ σ ]s) ≈ (ax-rhs ε [ σ ]s) ⦂ (ax-sort ε)
    ≡-⊢-≈ : ∀ {Γ : Context} {A} {s t : Term Γ A} → s ≡ t → ⊢ Γ ∥ s ≈ t ⦂ A
    ≡-⊢-≈ refl = eq-refl

    -- the action of the identity substitution is the identity
    id-action : ∀ {Γ : Context} {A} {a : Term Γ A} → (⊢ Γ ∥ a ≈ (a [ id-s ]s) ⦂ A)
    id-action {a = tm-var a} = eq-refl
    id-action {a = tm-oper f x} = eq-congr (λ i → id-action {a = x i})

    eq-axiom-id : ∀ (ε : ax) → ⊢ (ax-ctx ε ∥ ax-lhs ε ≈ ax-rhs ε ⦂  (ax-sort ε))
    eq-axiom-id ε = eq-tran id-action (eq-tran (eq-axiom ε id-s) (eq-symm id-action))

    eq-setoid : ∀ (Γ : Context) (A : sort) → Setoid (lsuc ℴ) (lsuc (ℓ ⊔ ℴ ⊔ 𝓈))
    eq-setoid Γ A =
      record
        { Carrier = Term Γ A
        ;  _≈_ = λ s t → (⊢ Γ ∥ s ≈ t ⦂ A)
        ; isEquivalence =
            record
              { refl = eq-refl
              ; sym = eq-symm
              ; trans = eq-tran
           }
        }
