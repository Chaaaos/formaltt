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
  record Axiom (Σ : Signature) : Set where
    field
      ax-ctx : Signature.Context Σ
      ax-sort : Signature.sort Σ
      ax-lhs : Signature.Term Σ ax-ctx ax-sort
      ax-rhs : Signature.Term Σ ax-ctx ax-sort

  -- Theory
  -- an equational theory is a family of equations over a given sort
  record Theory ℓ (Σ : Signature) : Set (lsuc ℓ) where
    open Signature Σ public
    field
      eq : Set ℓ -- the equations
      eq-ax : eq → Axiom Σ

    eq-ctx : eq → Context
    eq-ctx ε = Axiom.ax-ctx (eq-ax ε)

    eq-sort : eq → sort
    eq-sort ε = Axiom.ax-sort (eq-ax ε)

    eq-lhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε)
    eq-lhs ε = Axiom.ax-lhs (eq-ax ε)

    eq-rhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε)
    eq-rhs ε = Axiom.ax-rhs (eq-ax ε)

    -- equality of terms
    data eq-term : (Γ : Context) (A : sort) → Term Γ A → Term Γ A → Set (lsuc ℓ) where
      -- general rules
      eq-refl : ∀ {Γ A} {t : Term Γ A} → eq-term Γ A t t
      eq-symm : ∀ {Γ A} {s t : Term Γ A} → eq-term Γ A s t → eq-term Γ A t s
      eq-tran : ∀ {Γ A} {s t u : Term Γ A} → eq-term Γ A s t → eq-term Γ A t u → eq-term Γ A s u
      -- congruence rule
      eq-congr : ∀ {Γ} {f : oper} {xs ys : ∀ (i : arg (oper-arity f)) → Term Γ (sort-of (oper-arity f) i)} →
                (∀ i → eq-term Γ (sort-of (oper-arity f) i) (xs i)  (ys i)) → eq-term Γ (oper-sort f) (tm-oper f xs)  (tm-oper f ys)
      -- equational axiom
      eq-axiom : ∀ (ε : eq) {Γ : Context} (σ : Γ ⇒s eq-ctx ε) →
                 eq-term Γ (eq-sort ε) (eq-lhs ε [ σ ]s)  (eq-rhs ε [ σ ]s)

    syntax eq-term Γ A s t = Γ ⊢ s ≈ t ⦂ A
    infix 4 eq-term

    ≡-⊢-≈ : ∀ {Γ : Context} {A} {s t : Term Γ A} → s ≡ t → Γ ⊢ s ≈ t ⦂ A
    ≡-⊢-≈ refl = eq-refl

    -- the action of the identity substitution is the identity
    id-action : ∀ {Γ : Context} {A} {a : Term Γ A} → Γ ⊢ a ≈ a [ id-s ]s ⦂ A
    id-action {a = tm-var a} = eq-refl
    id-action {a = tm-oper f x} = eq-congr (λ i → id-action {a = x i})

    eq-axiom-id : ∀ (ε : eq) → eq-ctx ε ⊢ eq-lhs ε ≈ eq-rhs ε ⦂ eq-sort ε
    eq-axiom-id ε = eq-tran id-action (eq-tran (eq-axiom ε id-s) (eq-symm id-action))

    eq-setoid : ∀ (Γ : Context) (A : sort) → Setoid lzero (lsuc ℓ)
    eq-setoid Γ A =
      record
        { Carrier = Term Γ A
        ;  _≈_ = λ s t → Γ ⊢ s ≈ t ⦂ A
        ; isEquivalence =
            record
              { refl = eq-refl
              ; sym = eq-symm
              ; trans = eq-tran
           }
        }
