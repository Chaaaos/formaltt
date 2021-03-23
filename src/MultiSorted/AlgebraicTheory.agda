open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin

open import Relation.Binary

module MultiSorted.AlgebraicTheory where

  import MultiSorted.Context --  public

  -- Arity and arguments
  Arity : ∀ {Sort : Set} → Set
  Arity {Sort} =
               let open MultiSorted.Context in
               Context Sort

  arg : ∀ {Sort : Set} (A : Sort) → Arity {Sort} → Set
  arg {Sort} =
             let open MultiSorted.Context in
             var Sort

  -- an algebraic signature
  record Signature : Set₁ where
    field
      oper : Set -- operations
      sort : Set -- sorts
      oper-arity : oper → Arity {sort} -- the arity of an operation (with the sorts of the arguments)
      oper-sort : oper → sort -- the sort of an operation


  open Signature

  -- terms over a signature in a context of a given sort
  module _ (Σ : Signature) where

    open MultiSorted.Context (sort Σ) public
    data Term (Γ : Context ) : ∀ (A : sort Σ) → Set where
       tm-var : ∀ (A : sort Σ ) (x : var A Γ) → Term Γ A
       tm-oper : ∀ (f : oper Σ) → (∀ (A : sort Σ) → (arg A (oper-arity Σ f)) → Term Γ A) → Term Γ (oper-sort Σ f)

    -- Substitutions (definitions - some useful properties are in another file)
    substitution : ∀ (Γ Δ : Context) → Set
    substitution Γ Δ = ∀ (A : sort Σ) → var A Δ → Term Γ A

    -- -- identity substitution
    -- id-substitution : ∀ {Σ : Signature} {Γ : Context} → substitution Σ Γ Γ
    -- id-substitution = tm-var

    -- -- the action of a substitution on a term (contravariant)
    -- _[_]s : ∀ {Σ : Signature} {Γ Δ : Context} → Term {Σ} Δ → substitution Σ Γ Δ → Term {Σ} Γ
    -- (tm-var x) [ σ ]s = σ x
    -- (tm-oper f x) [ σ ]s = tm-oper f (λ i → x i [ σ ]s)

    -- infixr 6 _[_]s

    -- -- composition of substitutions
    -- _∘s_ : ∀ {Σ : Signature} {Γ Δ Θ : Context} → substitution Σ Δ Θ → substitution Σ Γ Δ → substitution Σ Γ Θ
    -- (σ ∘s ρ) x = σ x [ ρ ]s

    -- infixl 7 _∘s_

    -- -- Theory
    -- -- an equational theory is a family of equations over a given sort
    -- record Theory ℓ (Σ : Signature) : Set (lsuc ℓ) where
    --   field
    --     eq : Set ℓ -- the equations
    --     eq-ctx : ∀ (ε : eq) → Context -- the context of the equation ε
    --     eq-lhs : ∀ (ε : eq) → Term {Σ} (eq-ctx ε) -- the left-hand side
    --     eq-rhs : ∀ (ε : eq) → Term {Σ} (eq-ctx ε) -- the right-hand side

    --   infix 4 _⊢_≈_

    --   -- equality of terms
    --   data _⊢_≈_ : (Γ : Context) → Term Γ → Term Γ → Set (lsuc ℓ) where
    --     -- general rules
    --     eq-refl : ∀ {Γ} {t : Term Γ} → Γ ⊢ t ≈ t
    --     eq-symm : ∀ {Γ} {s t : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ s
    --     eq-tran : ∀ {Γ} {s t u : Term Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ u → Γ ⊢ s ≈ u
    --     -- congruence rule
    --     eq-congr : ∀ {Γ} {f : oper Σ} {xs ys : arg (oper-arity Σ f) → Term Γ} →
    --                (∀ i → Γ ⊢ xs i ≈ ys i) → Γ ⊢ tm-oper f xs ≈ tm-oper f ys
    --     -- equational axiom
    --     eq-axiom : ∀ (ε : eq) {Γ : Context} (σ : substitution Σ Γ (eq-ctx ε)) →
    --                Γ ⊢ eq-lhs ε [ σ ]s ≈ eq-rhs ε [ σ ]s

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
