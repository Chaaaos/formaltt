open import Agda.Primitive using (lzero; lsuc; _⊔_)

import SecondOrder.Arity
import SecondOrder.Context
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Term
import SecondOrder.Theory

module SecondOrder.Equality
  {ℓs ℓo ℓa}
  {𝔸 : SecondOrder.Arity.Arity}
  {Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸}
  (𝕋 : SecondOrder.Theory.Theory Σ ℓa)
  where

  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Theory.Theory 𝕋

  record Equality : Set (lsuc (ℓs ⊔ ℓo)) where
    constructor make-eq
    field
      eq-mv-ctx : MetaContext -- metavariable context of an equation
      eq-ctx : Context -- variable context of an equation
      eq-sort : sort -- sort of an equation
      eq-lhs : Term eq-mv-ctx eq-ctx eq-sort -- left-hand side
      eq-rhs : Term eq-mv-ctx eq-ctx eq-sort -- right-hand side
  infix 5 make-eq
  syntax make-eq Θ Γ A s t = Θ ⊕ Γ ∥ s ≈ t ⦂ A

  -- The equality judgement
  infix 4 ⊢_
  data ⊢_ : Equality → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
    -- general rules
    eq-refl : ∀ {Θ Γ A} {t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ t ≈ t ⦂ A
    eq-symm : ∀ {Θ Γ A} {s t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Γ ∥ t ≈ s ⦂ A
    eq-trans : ∀ {Θ Γ A} {s t u : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Γ ∥ t ≈ u ⦂ A → ⊢ Θ ⊕ Γ ∥ s ≈ u ⦂ A
    -- Congruence rule for operations
    -- the premises are: an operation f, two sets of arguments xs, ys of f that give
    -- for each argument of f a term in the extended context with the arguments that f binds
    -- such that xᵢ ≈ yᵢ for each i ∈ oper-arity f
    -- then f xs ≈ f ys (in the appropriate context)
    eq-congr : ∀ {Γ Θ} {f : oper}
                 {xs ys : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i)}
                 → (∀ i → ⊢ Θ ⊕ (Γ ,, arg-bind f i) ∥ (xs i) ≈ (ys i) ⦂ (arg-sort f i))
                 → ⊢ Θ ⊕ Γ ∥  (tm-oper f xs) ≈ (tm-oper f ys) ⦂ (oper-sort f)
    -- Congruence rule for metavariables
    -- the permises are: a meta-variable M, and two sets of arguments of the appropriate
    -- sorts and arities to apply M, such that xᵢ ≈ yᵢ
    -- then M xs ≈ M ys
    eq-congr-mv : ∀ {Γ Θ} {M : mv Θ} {xs ys : ∀ {B : sort} (i : mv-arg Θ M B) → Term Θ Γ B}
                → (∀ {B : sort} (i : mv-arg Θ M B)
                → ⊢ Θ ⊕ Γ ∥ (xs i) ≈ (ys i) ⦂ B)
                → ⊢ Θ ⊕ Γ ∥  (tm-meta M xs) ≈ (tm-meta M ys) ⦂ (mv-sort Θ M)
    -- equational axiom
    eq-axiom : ∀ (ε : ax) {Θ : MetaContext} {Γ : Context} (ι : Θ ⇒M (ax-mv-ctx ε) ⊕ Γ) →
               ⊢ Θ ⊕ Γ ∥ ( [ (rename-ctx-empty-r {Θ = Θ}) ]r (ax-lhs ε [ ι ]M)) ≈
                         ([ (rename-ctx-empty-r {Θ = Θ}) ]r (ax-rhs ε [ ι ]M)) ⦂ (ax-sort ε)

  --  terms and judgemental equality form a setoid
  eq-setoid : ∀ (Γ : Context) (Θ : MetaContext) (A : sort) → Setoid (lsuc (ℓo ⊔ ℓs ⊔ ℓa )) (lsuc (ℓ ⊔ ℓo ⊔ ℓs ⊔ ℓa))
  eq-setoid Γ Θ A =
    record
      { Carrier = Term Θ Γ A
      ;  _≈_ = λ s t → (⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A)
      ; isEquivalence =
                      record
                        { refl = eq-refl
                        ; sym = eq-symm
                        ; trans = eq-trans
                        }
        }

  -- equality of renamings
  _≈r_ : ∀ {Γ Δ : Context} {Θ} (σ τ : Θ ⊕ Γ ⇒r Δ) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa ⊔ ℓ))
  _≈r_ {Γ} {Δ} {Θ} σ τ = ∀ {A} (x : A ∈ Γ) → ⊢ Θ ⊕ Δ ∥ tm-var (σ x) ≈ tm-var (τ x) ⦂ A

  -- equality of substitutions
  _≈s_ : ∀ {Γ Δ : Context} {Θ} (σ τ : Θ ⊕ Δ ⇒s Γ) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa ⊔ ℓ))
  _≈s_ {Γ} {Δ} {Θ} σ τ = ∀ {A} (x : A ∈ Γ) → ⊢ Θ ⊕ Δ ∥ σ x ≈ τ x ⦂ A

  -- equality of metavariable instatiations
  _≈M_ : ∀ {Γ Θ ψ} (ι μ : _⇒M_⊕_ {Σ = Σ} ψ Θ Γ) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa ⊔ ℓ))
  _≈M_ {Γ} {Θ} {ψ} ι μ = ∀ (M : mv Θ) → ⊢ ψ ⊕ (Γ ,, mv-arity Θ M) ∥ ι M ≈ μ M ⦂ (mv-sort Θ M)
