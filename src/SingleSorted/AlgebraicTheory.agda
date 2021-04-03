open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin

open import Relation.Binary

module SingleSorted.AlgebraicTheory where

  open import SingleSorted.Context public

  Arity : Set
  Arity = Context

  arg : Arity → Set
  arg = var

  -- an algebraic signature
  record Signature : Set₁ where
    field
      oper : Set -- operations
      oper-arity : oper → Arity -- the arity of an operation

    -- terms over a signature in a context of a given sort
    data Term (Γ : Context) : Set where
      tm-var : var Γ → Term Γ
      tm-oper : ∀ (f : oper) → (arg (oper-arity f) → Term Γ) → Term Γ

    -- Substitutions (definitions - some useful properties are in another file)
    _⇒s_ : ∀ (Γ Δ : Context) → Set
    Γ ⇒s Δ = var Δ → Term Γ

    infix  4 _⇒s_

    -- identity substitution
    id-s : ∀ {Γ : Context} → Γ ⇒s Γ
    id-s = tm-var

    -- the action of a substitution on a term (contravariant)
    _[_]s : ∀ {Γ Δ : Context} → Term Δ → Γ ⇒s Δ → Term Γ
    (tm-var x) [ σ ]s = σ x
    (tm-oper f x) [ σ ]s = tm-oper f (λ i → x i [ σ ]s)

    infixr 6 _[_]s

    -- composition of substitutions
    _∘s_ : ∀ {Γ Δ Θ : Context} → Δ ⇒s Θ → Γ ⇒s Δ → Γ ⇒s Θ
    (σ ∘s ρ) x = σ x [ ρ ]s

    infixl 7 _∘s_

    -- Axioms are equations in context
    record Equation  : Set where
      field
        eq-ctx : Context
        eq-lhs : Term eq-ctx
        eq-rhs : Term eq-ctx

  -- Theory
  -- an equational theory is a family of equations over a given sort
  record Theory ℓ (Σ : Signature) : Set (lsuc ℓ) where
    open Signature Σ public

    field
      ax : Set ℓ -- the axiom names
      ax-eq : ax → Equation -- the axioms

    ax-ctx : ax → Context
    ax-ctx ε = Equation.eq-ctx (ax-eq ε)

    ax-lhs : ∀ (ε : ax) → Term (ax-ctx ε)
    ax-lhs ε = Equation.eq-lhs (ax-eq ε)

    ax-rhs : ∀ (ε : ax) → Term (ax-ctx ε)
    ax-rhs ε = Equation.eq-rhs (ax-eq ε)

    infix 4 _⊢_≈_

    -- equality of terms
    data _⊢_≈_ : (Γ : Context) → Term Γ → Term Γ → Set (lsuc ℓ) where
      -- general rules
      eq-refl : ∀ {Γ} {t : Term Γ} → Γ ⊢ t ≈ t
      eq-symm : ∀ {Γ} {s t : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ s
      eq-tran : ∀ {Γ} {s t u : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ u → Γ ⊢ s ≈ u
      -- congruence rule
      eq-congr : ∀ {Γ} {f : oper} {xs ys : arg (oper-arity f) → Term Γ} →
                 (∀ i → Γ ⊢ xs i ≈ ys i) → Γ ⊢ tm-oper f xs ≈ tm-oper f ys
      -- equational axiom
      eq-axiom : ∀ (ε : ax) {Γ : Context} (σ : Γ ⇒s (ax-ctx ε)) →
                 Γ ⊢ ax-lhs ε [ σ ]s ≈ ax-rhs ε [ σ ]s

    ≡-⊢-≈ : {Γ : Context} {s t : Term Γ} → s ≡ t → Γ ⊢ s ≈ t
    ≡-⊢-≈ refl = eq-refl

    -- the action of the identity substitution is the identity
    id-action : ∀ {Γ : Context} {a : Term Γ} → (Γ ⊢ a ≈ (a [ id-s ]s))
    id-action {a = tm-var a} = eq-refl
    id-action {a = tm-oper f x} = eq-congr (λ i → id-action {a = x i})

    eq-axiom-id : ∀ (ε : ax) → ax-ctx ε ⊢ ax-lhs ε ≈ ax-rhs ε
    eq-axiom-id ε = eq-tran id-action (eq-tran (eq-axiom ε id-s) (eq-symm id-action))

    eq-setoid : ∀ (Γ : Context) → Setoid lzero (lsuc ℓ)
    eq-setoid Γ =
      record
        { Carrier = Term Γ
        ;  _≈_ = λ s t → (Γ ⊢ s ≈ t)
        ; isEquivalence =
            record
              { refl = eq-refl
              ; sym = eq-symm
              ; trans = eq-tran
           }
        }
