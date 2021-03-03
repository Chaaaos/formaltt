open import Agda.Primitive
open import Agda.Builtin.Nat
open import Data.Fin

module SingleSorted.AlgebraicTheory where

-- an algebraic signature
record Signature : Set₁ where
  field
    oper : Set -- operations
    oper-arity : oper → Nat -- the arity of an operation

open Signature

-- A context is the same thing as a natural number (telling us how many variables are in the context)
Context = Nat

-- The empty context
empty-context = 0

-- The variables in context Γ are the elemnts of Fin Γ
var = Fin

-- It is absurd to have a variable in the empty context
empty-context-absurd : ∀ {ℓ} {A : Set ℓ} → var 0 → A
empty-context-absurd ()

-- terms over a signature in a context of a given sort
data Term {Σ : Signature} (Γ : Context) : Set where
  tm-var : var Γ → Term Γ
  tm-oper : ∀ (f : oper Σ) → (Fin (oper-arity Σ f) → Term {Σ} Γ) → Term {Σ} Γ

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
    eq-congr : ∀ {Γ} {f : oper Σ} {xs ys : Fin (oper-arity Σ f) → Term Γ} →
               (∀ i → Γ ⊢ xs i ≈ ys i) → Γ ⊢ tm-oper f xs ≈ tm-oper f ys
    -- equational axiom
    eq-axiom : ∀ (ε : eq) {Γ : Context} (σ : substitution Σ Γ (eq-ctx ε)) →
               Γ ⊢ eq-lhs ε [ σ ]s ≈ eq-rhs ε [ σ ]s

  -- equality of substitutions
  _≈s_ : ∀ {Γ Δ : Context} → substitution Σ Γ Δ → substitution Σ Γ Δ → Set (lsuc ℓ)
  _≈s_ {Γ = Γ} σ ρ = ∀ x → Γ ⊢ σ x ≈ ρ x

  -- symmetry of the equality of substitutions
  symm-subst : ∀ {Γ Δ : Context} {f g : substitution Σ Γ Δ} → f ≈s g → g ≈s f
  symm-subst {Γ} {Δ} {f} {g} p = λ x → eq-symm (p x)

  -- transitivity of the equality of substitutions
  trans-subst : ∀ {Γ Δ : Context} {f g h : substitution Σ Γ Δ} → f ≈s g → g ≈s h → f ≈s h
  trans-subst {Γ} {Δ} {f} {g} {h} p q = λ x → eq-tran (p x) (q x)

  -- neutrality of tm-var
  tm-var-id : ∀ {Γ : Context} {x : Term Γ} → Γ ⊢ x [ id-substitution ]s ≈ x
  tm-var-id {x = tm-var x} = eq-refl
  tm-var-id {x = tm-oper f x} = eq-congr (λ i → tm-var-id)

  -- any two substitutions into the empty context are equal
  empty-context-unique : ∀ {Γ : Context} {σ ρ : substitution Σ Γ empty-context} → σ ≈s ρ
  empty-context-unique ()

  -- composition of substitutions is functorial
  subst-∘s : ∀ {Γ Δ Θ} {ρ : substitution Σ Δ Γ} {σ : substitution Σ Θ Δ} (t : Term Γ) → Θ ⊢ (t [ ρ ]s) [ σ ]s ≈ t [ ρ ∘s σ ]s
  subst-∘s (tm-var x) = eq-refl
  subst-∘s (tm-oper f ts) = eq-congr (λ i → subst-∘s (ts i))

  -- substitution preserves equality
  eq-subst : ∀ {Γ Δ : Context} (σ : substitution Σ Γ Δ) {u v : Term Δ} → Δ ⊢ u ≈ v → Γ ⊢ u [ σ ]s ≈ v [ σ ]s
  eq-subst σ eq-refl = eq-refl
  eq-subst σ (eq-symm ξ) = eq-symm (eq-subst σ ξ)
  eq-subst σ (eq-tran ζ ξ) = eq-tran (eq-subst σ ζ) (eq-subst σ ξ)
  eq-subst σ (eq-congr ξ) = eq-congr (λ i → eq-subst σ (ξ i))
  eq-subst σ (eq-axiom ε ρ) = eq-tran (subst-∘s (eq-lhs ε)) (eq-tran (eq-axiom ε (ρ ∘s σ)) (eq-symm (subst-∘s (eq-rhs ε))))

 -- equivalent substitutions act the same on terms
  equiv-subst : ∀ {Γ Δ : Context} (f g : substitution Σ Γ Δ)  → f ≈s g → ( ∀ x → Γ ⊢ x [ f ]s ≈ x [ g ]s)
  equiv-subst f g p (tm-var x) = p x
  equiv-subst f g p (tm-oper f₁ x) = eq-congr (λ i → equiv-subst f g p (x i))

 -- equivalent substitution preserve equality
  equiv-eq-subst : ∀ {Γ Δ : Context} (f g : substitution Σ Γ Δ) {u v : Term Δ} (p : f ≈s g) → Δ ⊢ u ≈ v → Γ ⊢ u [ f ]s ≈ v [ g ]s
  equiv-eq-subst f g {u} {.u} p eq-refl = equiv-subst f g p u
  equiv-eq-subst f g {u} {v} p (eq-symm q) = eq-symm  (equiv-eq-subst g f {v} {u} (symm-subst p) q)
  equiv-eq-subst f g {u} {v} p (eq-tran {t = t} q q₁ ) =  eq-tran (eq-subst f q) (equiv-eq-subst f g {t} {v} (p) q₁)
  equiv-eq-subst {Γ} {Δ} f g {.(tm-oper _ _)} {.(tm-oper  _ _)} p (eq-congr x) = eq-congr λ i → equiv-eq-subst f g p (x i)
  equiv-eq-subst f g {.(eq-lhs ε [ σ ]s)} {.(eq-rhs ε [ σ ]s)} p (eq-axiom ε σ) = eq-tran (eq-subst f (eq-axiom ε σ)) (equiv-subst f g p (eq-rhs ε [ σ ]s))
