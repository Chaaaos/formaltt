open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin

open import Relation.Binary

import MultiSorted.Context as Context

module MultiSorted.AlgebraicTheory where

  -- an algebraic signature
  record Signature : Set₁ where
    field
      sort : Set -- sorts
      oper : Set -- operations

    open Context sort public

    -- Arity and arguments
    Arity : Set
    Arity = Context

    field
      oper-arity : oper → Arity -- the arity of an operation (with the sorts of the arguments)
      oper-sort : oper → sort -- the sort of an operation

    arg : Arity → Set
    arg = var

    arg-sort : ∀ (f : oper) → arg (oper-arity f) → sort
    arg-sort f = sort-of (oper-arity f)

    -- terms in a context of a given sort
    data Term (Γ : Context) : ∀ (A : sort) → Set where
      tm-var : ∀ (x : var Γ) → Term Γ (sort-of Γ x)
      tm-oper : ∀ (f : oper) → (∀ (i : arg (oper-arity f)) → Term Γ (arg-sort f i)) → Term Γ (oper-sort f)

    -- Substitutions (definitions - some useful properties are in another file)
    _⇒s_ : ∀ (Γ Δ : Context) → Set
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

  -- Axioms
  record Equation (Σ : Signature) : Set where
    constructor _∥_⦂_≈_
    field
      eq-ctx : Signature.Context Σ
      eq-sort : Signature.sort Σ
      eq-lhs : Signature.Term Σ eq-ctx eq-sort
      eq-rhs : Signature.Term Σ eq-ctx eq-sort
  infix 8 _∥_⦂_≈_

  -- Theory
  -- an equational theory is a family of equations over a given sort
  record Theory ℓ (Σ : Signature) : Set (lsuc ℓ) where
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
    data ⊢_ : Equation Σ → Set (lsuc ℓ) where
      -- general rules
      eq-refl : ∀ {Γ A} {t : Term Γ A} → ⊢ (Γ ∥ A ⦂ t ≈ t)
      eq-symm : ∀ {Γ A} {s t : Term Γ A} → ⊢ (Γ ∥ A ⦂ s ≈ t) → ⊢ (Γ ∥ A ⦂ t ≈ s)
      eq-tran : ∀ {Γ A} {s t u : Term Γ A} → ⊢ (Γ ∥ A ⦂ s ≈ t) → ⊢ (Γ ∥ A ⦂ t ≈ u) → ⊢ (Γ ∥ A ⦂ s ≈ u)
      -- congruence rule
      eq-congr : ∀ {Γ} {f : oper} {xs ys : ∀ (i : arg (oper-arity f)) → Term Γ (sort-of (oper-arity f) i)} →
                (∀ i → ⊢ (Γ ∥ (sort-of (oper-arity f) i) ⦂ (xs i) ≈ (ys i))) → ⊢ (Γ ∥ (oper-sort f) ⦂ (tm-oper f xs) ≈ (tm-oper f ys))
      -- equational axiom
      eq-axiom : ∀ (ε : ax) {Γ : Context} (σ : Γ ⇒s ax-ctx ε) →
                 ⊢ (Γ ∥ (ax-sort ε) ⦂ (ax-lhs ε [ σ ]s) ≈ (ax-rhs ε [ σ ]s))

    -- syntax eq-term Γ A s t = Γ ⊢ s ≈ t ⦂ A
    -- infix 4 eq-term

    -- I did not manage to have a nice syntax when I defined the equations, with the sort at the end of the jugement, and I have to fix the fixity in order to have less parenthesis

    ≡-⊢-≈ : ∀ {Γ : Context} {A} {s t : Term Γ A} → s ≡ t → ⊢ (Γ ∥ A ⦂ s ≈ t)
    ≡-⊢-≈ refl = eq-refl

    -- the action of the identity substitution is the identity
    id-action : ∀ {Γ : Context} {A} {a : Term Γ A} → (⊢ (Γ ∥ A ⦂ a ≈ (a [ id-s ]s)))
    id-action {a = tm-var a} = eq-refl
    id-action {a = tm-oper f x} = eq-congr (λ i → id-action {a = x i})

    eq-axiom-id : ∀ (ε : ax) → ⊢ (ax-ctx ε ∥ (ax-sort ε) ⦂ ax-lhs ε ≈ ax-rhs ε)
    eq-axiom-id ε = eq-tran id-action (eq-tran (eq-axiom ε id-s) (eq-symm id-action))

    eq-setoid : ∀ (Γ : Context) (A : sort) → Setoid lzero (lsuc ℓ)
    eq-setoid Γ A =
      record
        { Carrier = Term Γ A
        ;  _≈_ = λ s t → (⊢ (Γ ∥ A ⦂ s ≈ t))
        ; isEquivalence =
            record
              { refl = eq-refl
              ; sym = eq-symm
              ; trans = eq-tran
           }
        }
