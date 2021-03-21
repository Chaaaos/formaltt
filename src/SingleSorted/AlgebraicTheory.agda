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

  open Signature

  -- terms over a signature in a context of a given sort
  data Term {Σ : Signature} (Γ : Context) : Set where
    tm-var : var Γ → Term Γ
    tm-oper : ∀ (f : oper Σ) → (arg (oper-arity Σ f) → Term {Σ} Γ) → Term {Σ} Γ

  -- Substitutions (definitions - some useful properties are in another file)
  substitution : ∀ (Σ : Signature) (Γ Δ : Context) → Set
  substitution Σ Γ Δ = var Δ → Term {Σ} Γ

  -- identity substitution
  id-substitution : ∀ {Σ : Signature} {Γ : Context} → substitution Σ Γ Γ
  id-substitution = tm-var

  -- the action of a substitution on a term (contravariant)
  _[_]s : ∀ {Σ : Signature} {Γ Δ : Context} → Term {Σ} Δ → substitution Σ Γ Δ → Term {Σ} Γ
  (tm-var x) [ σ ]s = σ x
  (tm-oper f x) [ σ ]s = tm-oper f (λ i → x i [ σ ]s)

  infixr 6 _[_]s

  -- composition of substitutions
  _∘s_ : ∀ {Σ : Signature} {Γ Δ Θ : Context} → substitution Σ Δ Θ → substitution Σ Γ Δ → substitution Σ Γ Θ
  (σ ∘s ρ) x = σ x [ ρ ]s

  infixl 7 _∘s_

  -- Theory
  -- an equational theory is a family of equations over a given sort
  record Theory ℓ (Σ : Signature) : Set (lsuc ℓ) where
    field
      eq : Set ℓ -- the equations
      eq-ctx : ∀ (ε : eq) → Context -- the context of the equation ε
      eq-lhs : ∀ (ε : eq) → Term {Σ} (eq-ctx ε) -- the left-hand side
      eq-rhs : ∀ (ε : eq) → Term {Σ} (eq-ctx ε) -- the right-hand side

    infix 4 _⊢_≈_

    -- equality of terms
    data _⊢_≈_ : (Γ : Context) → Term Γ → Term Γ → Set (lsuc ℓ) where
      -- general rules
      eq-refl : ∀ {Γ} {t : Term Γ} → Γ ⊢ t ≈ t
      eq-symm : ∀ {Γ} {s t : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ s
      eq-tran : ∀ {Γ} {s t u : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ u → Γ ⊢ s ≈ u
      -- congruence rule
      eq-congr : ∀ {Γ} {f : oper Σ} {xs ys : arg (oper-arity Σ f) → Term Γ} →
                 (∀ i → Γ ⊢ xs i ≈ ys i) → Γ ⊢ tm-oper f xs ≈ tm-oper f ys
      -- equational axiom
      eq-axiom : ∀ (ε : eq) {Γ : Context} (σ : substitution Σ Γ (eq-ctx ε)) →
                 Γ ⊢ eq-lhs ε [ σ ]s ≈ eq-rhs ε [ σ ]s

    ≡-⊢-≈ : {Γ : Context} {s t : Term Γ} → s ≡ t → Γ ⊢ s ≈ t
    ≡-⊢-≈ refl = eq-refl

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
