open import Agda.Primitive

open import Equality
open import Finite
open import Category

module SingleSortedAlgebra where

  -- an algebraic signature
  record Signature : Set₁ where
    field
      op : Set -- operations
      op-arity : op → ℕ -- the arity of an operation

  open Signature

  Context = ℕ
  var = Fin

  -- terms over a signature in a context of a given sort
  data Term (Σ : Signature) (Γ : Context) : Set where
    tm-var : ∀ (x : var Γ) → Term Σ Γ
    tm-op : ∀ (f : op Σ) → (∀ (i : Fin (op-arity Σ f)) → Term Σ Γ) → Term Σ Γ

  substitution : ∀ (Σ : Signature) (Γ Δ : Context) → Set
  substitution Σ Γ Δ = var Γ → Term Σ Δ

  -- the action of a substitution on a term
  _·_ : ∀ {Σ : Signature} {Γ Δ : Context} → substitution Σ Γ Δ → Term Σ Γ → Term Σ Δ
  σ · (tm-var x) = σ x
  σ · (tm-op f x) = tm-op f (λ i → σ · x i)

  infixr 6 _·_

  -- composition of substitutions
  _○_ : ∀ {Σ : Signature} {Γ Δ Θ : Context} → substitution Σ Δ Θ → substitution Σ Γ Δ → substitution Σ Γ Θ
  (σ ○ τ) x = σ · τ x

  infixl 7 _○_

  -- an equational theory is a family of equations over a given sort
  record Theory ℓ (Σ : Signature) : Set (lsuc ℓ) where
    field
      eq : Set ℓ
      eq-ctx : ∀ (ε : eq) → Context
      eq-lhs : ∀ (ε : eq) → Term Σ (eq-ctx ε)
      eq-rhs : ∀ (ε : eq) → Term Σ (eq-ctx ε)

  open Theory

  infix 4 _∥_⊢_≈_

  -- equality of terms
  data _∥_⊢_≈_ {ℓ} {Σ : Signature} (T : Theory ℓ Σ) : (Γ : Context) → Term Σ Γ → Term Σ Γ → Set (lsuc ℓ) where
    -- general rules
    eq-refl : ∀ {Γ} {t : Term Σ Γ} → T ∥ Γ ⊢ t ≈ t
    eq-symm : ∀ {Γ} {s t : Term Σ Γ} → T ∥ Γ ⊢ s ≈ t → T ∥ Γ ⊢ t ≈ s
    eq-tran : ∀ {Γ} {s t u : Term Σ Γ} → T ∥ Γ ⊢ s ≈ t → T ∥ Γ ⊢ t ≈ u → T ∥ Γ ⊢ s ≈ u
    -- congruence rule
    eq-congr : ∀ {Γ} {f : op Σ} (x y : ∀ (i : Fin (op-arity Σ f)) → Term Σ Γ) →
               (∀ i → T ∥ Γ ⊢ x i ≈ y i) → T ∥ Γ ⊢ tm-op f x ≈ tm-op f y
    -- equational axiom
    eq-axiom : ∀ (ε : eq T) {Δ : Context} (σ : substitution Σ (eq-ctx T ε) Δ) →
               T ∥ Δ ⊢ σ · (eq-lhs T ε) ≈ σ · eq-rhs T ε

  -- composition is functorial
  subst-○ : ∀ {ℓ} {Σ : Signature} {T : Theory ℓ Σ} {Γ Δ Θ : Context}
              (σ : substitution Σ Δ Θ) (τ : substitution Σ Γ Δ) →
              ∀ (t : Term Σ Γ) → T ∥ Θ ⊢ (σ · τ · t) ≈ (σ ○ τ · t)
  subst-○ σ τ (tm-var x) = eq-refl
  subst-○ σ τ (tm-op f x) = eq-congr (λ i → σ · τ · x i) (λ i → σ ○ τ · x i) λ i → subst-○ σ τ (x i)

  -- substitution preserves equality
  eq-subst : ∀ {ℓ} {Σ : Signature} {T : Theory ℓ Σ} {Γ Δ : Context} (σ : substitution Σ Γ Δ)
               {s t : Term Σ Γ} → T ∥ Γ ⊢ s ≈ t → T ∥ Δ ⊢ σ · s ≈ σ · t
  eq-subst σ eq-refl = eq-refl
  eq-subst σ (eq-symm ξ) = eq-symm (eq-subst σ ξ)
  eq-subst σ (eq-tran ζ ξ) = eq-tran (eq-subst σ ζ) (eq-subst σ ξ)
  eq-subst σ (eq-congr x y ξ) = eq-congr (λ i → σ · x i) (λ i → σ · y i) λ i → eq-subst σ (ξ i)
  eq-subst {T = T} σ (eq-axiom ε τ) =
    eq-tran (subst-○ σ τ (eq-lhs T ε))
            (eq-tran (eq-axiom ε (σ ○ τ)) (eq-symm (subst-○ σ τ (eq-rhs T ε))))

  open Category.Category
  open Category.FPCategory

  record Interp {ℓ} (Σ : Signature) (C : FPCategory ℓ) : Set ℓ where
    field
      interp-carrier : obj (category C)
      interp-op : ∀ (f : op Σ) → hom (category C) (power C (op-arity Σ f) interp-carrier) interp-carrier

    -- the interpretation of a term
    interp-term : ∀ {Γ : Context} → Term Σ Γ → hom (category C) (power C Γ interp-carrier) interp-carrier
    interp-term {Γ} (tm-var x) = project C Γ x
    interp-term {Γ} (tm-op f ts) = compose (category C) (interp-op f) (tuple C (op-arity Σ f) (λ i → interp-term (ts i)))

  -- Homomorphism of interpretations
  record InterpHom {ℓ} {Σ : Signature} {C : FPCategory ℓ} (A B : Interp Σ C) : Set ℓ where
    open Interp

    field
      interp-hom : hom (category C) (interp-carrier A) (interp-carrier B)
      interp-hom-eq :
        ∀ {f : op Σ} →
        compose (category C) interp-hom (interp-op A f) ≡ compose (category C) (interp-op B f) (power-hom C (op-arity Σ f) interp-hom)

  -- Every signature has the trivial interpretation

  TrivialInterp : ∀ {ℓ} (Σ : Signature) (C : FPCategory ℓ) → Interp Σ C
  TrivialInterp Σ C =
    record
      { interp-carrier = terminal-obj C
      ; interp-op = λ f → terminal-hom C
      }

  -- The identity homomorphism
  Id : ∀ {ℓ} {Σ : Signature} {C : FPCategory ℓ} (A : Interp Σ C) → InterpHom A A
  Id {C = C} A =
    record
      { interp-hom = id-hom (category C)
      ; interp-hom-eq = λ {f} → tran (compose-id-left (category C))
                             (tran (sym (compose-id-right (category C)))
                                   (ap
                                     (sym (tuple-project C
                                           (λ i → tran (project-tuple C)
                                                 (tran (compose-id-left (category C))
                                                       (sym (compose-id-right (category C)))))))))
      }

  -- Compositon of homomorphisms
  HomCompose : ∀ {ℓ} {Σ : Signature} {C : FPCategory ℓ} {A B C : Interp Σ C} → InterpHom B C → InterpHom A B → InterpHom A C
  HomCompose {C = C} ϕ ψ =
      record
        { interp-hom = compose (category C) (interp-hom ϕ) (interp-hom ψ)
        ; interp-hom-eq = λ {f} → {!!}
        }
      where open InterpHom


  -- Model of a theory
  record Model {ℓT ℓC} {Σ : Signature} (T : Theory ℓT Σ) (C : FPCategory ℓC) : Set (ℓT ⊔ ℓC) where
    open Interp

    field
      {{model-interp}} : Interp Σ C
      model-eq : ∀ (ε : eq T) → interp-term model-interp (eq-lhs T ε) ≡ interp-term model-interp (eq-rhs T ε)

  -- Every theory has the trivial model, whose carrier is the terminal object

  TrivialModel : ∀ {ℓT ℓC} {Σ : Signature} (T : Theory ℓT Σ) (C : FPCategory ℓC) → Model T C
  TrivialModel {Σ = Σ} T C =
    record
      { model-interp = TrivialInterp Σ C
      ; model-eq = λ ε → terminal-eq C
      }
