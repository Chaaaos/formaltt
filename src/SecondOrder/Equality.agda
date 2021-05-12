open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Renaming
import SecondOrder.Term
import SecondOrder.Substitution
import SecondOrder.Instantiation
import SecondOrder.Theory

module SecondOrder.Equality
  {ℓs ℓo ℓa}
  {𝔸 : SecondOrder.Arity.Arity}
  {Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸}
  (𝕋 : SecondOrder.Theory.Theory Σ ℓa)
  where

  open SecondOrder.Metavariable Σ
  open SecondOrder.Renaming Σ
  open SecondOrder.Term Σ
  open SecondOrder.Substitution Σ
  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Instantiation Σ
  open SecondOrder.Theory.Theory 𝕋

  record Equation : Set (lsuc (ℓs ⊔ ℓo)) where
    constructor make-eq
    field
      eq-mv-ctx : MetaContext -- metavariable context of an equation
      eq-ctx : Context -- variable context of an equation
      eq-sort : sort -- sort of an equation
      eq-lhs : Term eq-mv-ctx eq-ctx eq-sort -- left-hand side
      eq-rhs : Term eq-mv-ctx eq-ctx eq-sort -- right-hand side

  infix 5 make-eq

  syntax make-eq Θ Γ A s t = Θ ⊕ Γ ∥ s ≋ t ⦂ A

  -- Instantiate an axiom of 𝕋 to an equation
  instantiate-axiom : ∀ (ε : ax) {Θ Γ} (I : ax-mv-ctx ε ⇒ⁱ Θ ⊕ Γ) → Equation
  instantiate-axiom ε {Θ} {Γ} I =
     Θ ⊕ Γ ∥ instantiate-closed-term I (ax-lhs ε) ≋  instantiate-closed-term I (ax-rhs ε) ⦂ ax-sort ε


  -- The equality judgement

  infix 4 ⊢_

  data ⊢_ : Equation → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
    -- general rules
    eq-refl : ∀ {Θ Γ A} {t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ t ≋ t ⦂ A
    eq-symm : ∀ {Θ Γ A} {s t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ s ≋ t ⦂ A → ⊢ Θ ⊕ Γ ∥ t ≋ s ⦂ A
    eq-trans : ∀ {Θ Γ A} {s t u : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ s ≋ t ⦂ A → ⊢ Θ ⊕ Γ ∥ t ≋ u ⦂ A → ⊢ Θ ⊕ Γ ∥ s ≋ u ⦂ A

    -- Congruence rule for operations
    -- the premises are: an operation f, two sets of arguments xs, ys of f that give
    -- for each argument of f a term in the extended context with the arguments that f binds
    -- such that xᵢ ≋ yᵢ for each i ∈ oper-arity f
    -- then f xs ≋ f ys (in the appropriate context)
    eq-oper : ∀ {Γ Θ} {f : oper}
                 {xs ys : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i)}
                 → (∀ i → ⊢ Θ ⊕ (Γ ,, arg-bind f i) ∥ (xs i) ≋ (ys i) ⦂ (arg-sort f i))
                 → ⊢ Θ ⊕ Γ ∥  (tm-oper f xs) ≋ (tm-oper f ys) ⦂ (oper-sort f)
    -- Congruence rule for metavariables
    -- the permises are: a meta-variable M, and two sets of arguments of the appropriate
    -- sorts and arities to apply M, such that xᵢ ≋ yᵢ
    -- then M xs ≋ M ys
    eq-meta : ∀ {Γ Θ} {M : mv Θ} {xs ys : ∀ {B : sort} (i : mv-arg Θ M B) → Term Θ Γ B}
                → (∀ {B : sort} (i : mv-arg Θ M B)
                → ⊢ Θ ⊕ Γ ∥ (xs i) ≋ (ys i) ⦂ B)
                → ⊢ Θ ⊕ Γ ∥  (tm-meta M xs) ≋ (tm-meta M ys) ⦂ (mv-sort Θ M)
    -- equational axiom
    eq-axiom : ∀ (ε : ax) {Θ Γ} (I : ax-mv-ctx ε ⇒ⁱ Θ ⊕ Γ) → ⊢ instantiate-axiom ε I

  -- Syntactically equal terms are judgementally equal
  ≈-≋ : ∀ {Θ Γ A} {s t : Term Θ Γ A} → s ≈ t → ⊢ Θ ⊕ Γ ∥ s ≋ t ⦂ A
  ≈-≋ (≈-≡ refl) = eq-refl
  ≈-≋ (≈-meta ξ) = eq-meta (λ i → ≈-≋ (ξ i))
  ≈-≋ (≈-oper ξ) = eq-oper (λ i → ≈-≋ (ξ i))


  --  terms and judgemental equality form a setoid
  eq-setoid : ∀ (Γ : Context) (Θ : MetaContext) (A : sort) → Setoid (lsuc (ℓo ⊔ ℓs)) (lsuc (ℓo ⊔ ℓs ⊔ ℓa))
  eq-setoid Γ Θ A =
    record
      { Carrier = Term Θ Γ A
      ;  _≈_ = λ s t → ⊢ Θ ⊕ Γ ∥ s ≋ t ⦂ A
      ; isEquivalence =
                      record
                        { refl = eq-refl
                        ; sym = eq-symm
                        ; trans = eq-trans
                        }
        }

  -- judgemental equality of substitutions
  _≋ˢ_ : ∀ {Θ Γ Δ} (σ τ : Θ ⊕ Γ ⇒ˢ Δ) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
  _≋ˢ_ {Θ} {Γ} {Δ} σ τ = ∀ {A} (x : A ∈ Γ) → ⊢ Θ ⊕ Δ ∥ σ x ≋ τ x ⦂ A

  ≈ˢ-≋ˢ : ∀ {Θ Γ Δ} {σ τ : Θ ⊕ Γ ⇒ˢ Δ} → σ ≈ˢ τ → σ ≋ˢ τ
  ≈ˢ-≋ˢ ξ = λ x → ≈-≋ (ξ x)

  -- judgemental equality of metavariable instatiations
  _≋ⁱ_ : ∀ {Θ Ξ Γ} (I J : Θ ⇒ⁱ Ξ ⊕ Γ) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
  _≋ⁱ_ {Θ} {Ξ} {Γ} I J = ∀ (M : mv Θ) → ⊢ Ξ ⊕ (Γ ,, mv-arity Θ M) ∥ I M ≋ J M ⦂ mv-sort Θ M
