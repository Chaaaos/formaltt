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

  -- terms over a signature in a context of a given sort
  module _ (Σ : Signature) where
    open Signature Σ

    data Term (Γ : Context) : ∀ (A : sort) → Set where
       tm-var : ∀ (x : var Γ) → Term Γ (sort-of Γ x)
       tm-oper : ∀ (f : oper) → (∀ (i : arg (oper-arity f)) → Term Γ (arg-sort f i)) → Term Γ (oper-sort f)

    -- Substitutions (definitions - some useful properties are in another file)
    substitution : ∀ (Γ Δ : Context) → Set
    substitution Γ Δ = ∀ (x : var Δ) → Term Γ (sort-of Δ x)

    -- identity substitution
    id-substitution : ∀ {Σ : Signature} {Γ : Context} → substitution Γ Γ
    id-substitution = tm-var

    -- the action of a substitution on a term (contravariant)
    _[_]s : ∀ {Γ Δ : Context} {A : sort} → Term Δ A → substitution Γ Δ → Term Γ A
    (tm-var x) [ σ ]s = σ x
    (tm-oper f ts) [ σ ]s = tm-oper f (λ i → ts i [ σ ]s)

    infixr 6 _[_]s

    -- composition of substitutions
    _∘s_ : ∀ {Γ Δ Θ : Context} → substitution Δ Θ → substitution Γ Δ → substitution Γ Θ
    (σ ∘s ρ) x = σ x [ ρ ]s

    infixl 7 _∘s_

    -- Theory
    -- an equational theory is a family of equations over a given sort
    record Theory ℓ (Σ : Signature) : Set (lsuc ℓ) where
      field
        eq : Set ℓ -- the equations
        eq-ctx : eq → Context -- the context of the equation ε
        eq-sort : eq → sort -- the sort of the left-hand and right-hand sides
        eq-lhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε) -- the left-hand side
        eq-rhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε) -- the right-hand side

      -- equality of terms
      data eq-term : (Γ : Context) (A : sort) → Term Γ A → Term Γ A → Set (lsuc ℓ) where
        -- general rules
        eq-refl : ∀ {Γ A} {t : Term Γ A} → eq-term Γ A t t
        -- eq-symm : ∀ {Γ} {s t : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ s
        -- eq-tran : ∀ {Γ} {s t u : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ u → Γ ⊢ s ≈ u
        -- -- congruence rule
        -- eq-congr : ∀ {Γ} {f : oper Σ} {xs ys : arg (oper-arity Σ f) → Term Γ} →
        --            (∀ i → Γ ⊢ xs i ≈ ys i) → Γ ⊢ tm-oper f xs ≈ tm-oper f ys
        -- -- equational axiom
        -- eq-axiom : ∀ (ε : eq) {Γ : Context} (σ : substitution Σ Γ (eq-ctx ε)) →
        --            Γ ⊢ eq-lhs ε [ σ ]s ≈ eq-rhs ε [ σ ]s

      infix 4 _⊢_≈_::_

      syntax eq-term Γ A s t = Γ ⊢ s ≈ t :: A

    --   ≡-⊢-≈ : {Γ : Context} {s t : Term Γ} → s ≡ t → Γ ⊢ s ≈ t
    --   ≡-⊢-≈ refl = eq-refl

    --   -- the action of the identity substitution is the identity
    --   id-action : ∀ {Γ : Context} {a : Term Γ} → (Γ ⊢ a ≈ (a [ id-substitution ]s))
    --   id-action {a = tm-var a} = eq-refl
    --   id-action {a = tm-oper f x} = eq-congr (λ i → id-action {a = x i})

    --   eq-axiom-id : ∀ (ε : eq) → eq-ctx ε ⊢ eq-lhs ε ≈ eq-rhs ε
    --   eq-axiom-id ε = eq-tran id-action (eq-tran (eq-axiom ε id-substitution) (eq-symm id-action))

    --   eq-setoid : ∀ (Γ : Context) → Setoid lzero (lsuc ℓ)
    --   eq-setoid Γ =
    --     record
    --       { Carrier = Term Γ
    --       ;  _≈_ = λ s t → (Γ ⊢ s ≈ t)
    --       ; isEquivalence =
    --           record
    --             { refl = eq-refl
    --             ; sym = eq-symm
    --             ; trans = eq-tran
    --          }
    --       }
