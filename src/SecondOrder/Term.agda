open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable

module SecondOrder.Term
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ

  -- The term judgement
  data Term (Θ : MContext) : ∀ (Γ : VContext) (A : sort) → Set ℓ

  Arg : ∀ (Θ : MContext) (Γ : VContext) (A : sort) (Δ : VContext) → Set ℓ
  Arg Θ Γ A Δ = Term Θ (Γ ,, Δ) A

  data Term Θ where
    tm-var : ∀ {Γ} {A} (x : A ∈ Γ) → Term Θ Γ A
    tm-meta : ∀ {α A} {Γ} (M : [ α , A ]∈ Θ)
                (ts : ∀ {B} (i : B ∈ α) → Term Θ Γ B)
                → Term Θ Γ A
    tm-oper : ∀ {Γ} (f : oper) (es : ∀ (i : oper-arg f) → Arg Θ Γ (arg-sort f i) (arg-bind f i))
                → Term Θ Γ (oper-sort f)

  -- Syntactic equality of terms

  infix 4 _≈_

  data _≈_ {Θ : MContext} : ∀ {Γ : VContext} {A : sort} → Term Θ Γ A → Term Θ Γ A → Set ℓ where
    ≈-≡ : ∀ {Γ A} {t u : Term Θ Γ A} (ξ : t ≡ u) → t ≈ u
    ≈-meta : ∀ {Γ} {α A} {M : [ α , A ]∈ Θ} {ts us : ∀ {B} (i : B ∈ α) → Term Θ Γ B}
               (ξ : ∀ {B} i → ts {B} i ≈ us {B} i) → tm-meta M ts ≈ tm-meta M us
    ≈-oper : ∀ {Γ} {f : oper} {ds es : ∀ (i : oper-arg f) → Arg Θ Γ (arg-sort f i)  (arg-bind f i)}
               (ξ : ∀ i → ds i ≈ es i) → tm-oper f ds ≈ tm-oper f es

  ≈-refl : ∀ {Θ Γ A} {t : Term Θ Γ A} → t ≈ t
  ≈-refl = ≈-≡ refl

  ≈-sym : ∀ {Θ Γ A} {t u : Term Θ Γ A} → t ≈ u → u ≈ t
  ≈-sym (≈-≡ refl) = ≈-≡ refl
  ≈-sym (≈-meta ξ) = ≈-meta λ i → ≈-sym (ξ i)
  ≈-sym (≈-oper ξ) = ≈-oper (λ i → ≈-sym (ξ i))

  ≈-trans : ∀ {Θ Γ A} {t u v : Term Θ Γ A} → t ≈ u → u ≈ v → t ≈ v
  ≈-trans (≈-≡ refl) ξ = ξ
  ≈-trans (≈-meta ζ) (≈-≡ refl) = ≈-meta ζ
  ≈-trans (≈-meta ζ) (≈-meta ξ) = ≈-meta (λ i → ≈-trans (ζ i) (ξ i))
  ≈-trans (≈-oper ζ) (≈-≡ refl) = ≈-oper ζ
  ≈-trans (≈-oper ζ) (≈-oper ξ) = ≈-oper (λ i → ≈-trans (ζ i) (ξ i))

  Term-setoid : ∀ (Θ : MContext) (Γ : VContext)  (A : sort) → Setoid ℓ ℓ
  Term-setoid Θ Γ A =
    record
      { Carrier = Term Θ Γ A
      ; _≈_ = _≈_
      ; isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans } }

  -- to equal variable give rise to two equal terms
  ≡-var : ∀ {Θ Γ A} → {s t : A ∈ Γ} → s ≡ t → tm-var {Θ = Θ} s ≡ tm-var t
  ≡-var refl = refl
