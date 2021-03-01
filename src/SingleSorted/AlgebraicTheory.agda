open import Agda.Primitive
open import Agda.Builtin.Nat
open import Data.Fin

open import Categories.Category
open import Categories.Category.Cartesian

module SingleSorted.AlgebraicTheory where

-- an algebraic signature
record Signature : Set₁ where
  field
    oper : Set -- operations
    oper-arity : oper → Nat -- the arity of an operation

open Signature

-- A context is the same thing as a natural number (telling us how many variables are in the context)
Context = Nat

-- The variables in context Γ are the elemnts of Fin Γ
var = Fin

-- terms over a signature in a context of a given sort
data Term {Σ : Signature} (Γ : Context) : Set where
  tm-var : ∀ (x : var Γ) → Term Γ
  tm-oper : ∀ (f : oper Σ) → (Fin (oper-arity Σ f) → Term {Σ} Γ) → Term {Σ} Γ

substitution : ∀ (Σ : Signature) (Γ Δ : Context) → Set
substitution Σ Γ Δ = var Γ → Term {Σ} Δ

-- identity substitution
id-substitution : ∀ {Σ : Signature} {Γ : Context} → substitution Σ Γ Γ
id-substitution = tm-var

-- the action of a substitution on a term
_·_ : ∀ {Σ : Signature} {Γ Δ : Context} → substitution Σ Γ Δ → Term Γ → Term Δ
σ · (tm-var x) = σ x
σ · (tm-oper f x) = tm-oper f (λ i → σ · x i)

infixr 6 _·_

-- composition of substitutions
_∘s_ : ∀ {Σ : Signature} {Γ Δ Θ : Context} → substitution Σ Δ Θ → substitution Σ Γ Δ → substitution Σ Γ Θ
(σ ∘s τ) x = σ · τ x

infixl 7 _∘s_

-- an equational theory is a family of equations over a given sort
record Theory ℓ (Σ : Signature) : Set (lsuc ℓ) where
  field
    eq : Set ℓ -- the equations
    eq-ctx : ∀ (ε : eq) → Context -- the context of the equation ε
    eq-lhs : ∀ (ε : eq) → Term (eq-ctx ε) -- the left-hand side
    eq-rhs : ∀ (ε : eq) → Term (eq-ctx ε) -- the right-hand side

  infix 4 _⊢_≈_

  -- equality of terms
  data _⊢_≈_ : (Γ : Context) → Term Γ → Term Γ → Set (lsuc ℓ) where
    -- general rules
    eq-refl : ∀ {Γ} {t : Term Γ} → Γ ⊢ t ≈ t
    eq-symm : ∀ {Γ} {s t : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ s
    eq-tran : ∀ {Γ} {s t u : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ u → Γ ⊢ s ≈ u
    -- congruence rule
    eq-congr : ∀ {Γ} {f : oper Σ} (x y : Fin (oper-arity Σ f) → Term Γ) →
               (∀ i → Γ ⊢ x i ≈ y i) → Γ ⊢ tm-oper f x ≈ tm-oper f y
    -- equational axiom
    eq-axiom : ∀ (ε : eq) {Δ : Context} (σ : substitution Σ (eq-ctx ε) Δ) →
               Δ ⊢ σ · (eq-lhs ε) ≈ σ · eq-rhs ε

  -- equality of substitutions
  _≈s_ : ∀ {Γ Δ : Context} → substitution Σ Γ Δ → substitution Σ Γ Δ → Set (lsuc ℓ)
  _≈s_ {Δ = Δ} σ ρ = ∀ x → Δ ⊢ σ x ≈ ρ x

  -- composition of substitutions is functorial
  subst-∘s : ∀ {Γ Δ Θ} (σ : substitution Σ Δ Θ) (τ : substitution Σ Γ Δ) → ∀ (t : Term Γ) → Θ ⊢ (σ · τ · t) ≈ (σ ∘s τ · t)
  subst-∘s σ τ (tm-var x) = eq-refl
  subst-∘s σ τ (tm-oper f x) = eq-congr (λ i → σ · τ · x i) (λ i → σ ∘s τ · x i) λ i → subst-∘s σ τ (x i)

  -- substitution preserves equality
  eq-subst : ∀ {Γ Δ : Context} (σ : substitution Σ Γ Δ) {s t : Term Γ} → Γ ⊢ s ≈ t → Δ ⊢ σ · s ≈ σ · t
  eq-subst σ eq-refl = eq-refl
  eq-subst σ (eq-symm ξ) = eq-symm (eq-subst σ ξ)
  eq-subst σ (eq-tran ζ ξ) = eq-tran (eq-subst σ ζ) (eq-subst σ ξ)
  eq-subst σ (eq-congr x y ξ) = eq-congr (λ i → σ · x i) (λ i → σ · y i) λ i → eq-subst σ (ξ i)
  eq-subst σ (eq-axiom ε τ) =
    eq-tran (subst-∘s σ τ (eq-lhs ε))
            (eq-tran (eq-axiom ε (σ ∘s τ)) (eq-symm (subst-∘s σ τ (eq-rhs ε))))
