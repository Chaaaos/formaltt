open import Agda.Primitive using (lzero; lsuc; _⊔_)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Renaming
import SecondOrder.Term

module SecondOrder.Substitution
  {ℓs ℓo}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.Renaming Σ

  -- substitition

  infix 4 _⊕_⇒s_

  _⊕_⇒s_ : ∀ (Θ : MetaContext) (Γ Δ : Context) → Set (lsuc (ℓs ⊔ ℓo))
  Θ ⊕ Γ ⇒s Δ = ∀ {A} (x : A ∈ Δ) → Term Θ Γ A

  -- identity substitution
  id-s : ∀ {Θ Γ} → Θ ⊕ Γ ⇒s Γ
  id-s = tm-var

  module _ {Θ : MetaContext}  where

    -- the join of substitutions
    infixl 7 _⋈s_

    _⋈s_ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒s Δ → Θ ⊕ Γ ⇒s Ξ → Θ ⊕ Γ ⇒s Δ ,, Ξ
    (σ ⋈s τ) (var-inl x) = σ x
    (σ ⋈s τ) (var-inr y) = τ y

    -- the sum of substitutions

    infixl 8 _+s_

    _+s_ : ∀ {Γ Γ' Δ Δ'} → Θ ⊕ Γ ⇒s Δ → Θ ⊕ Γ' ⇒s Δ' → Θ ⊕ (Γ ,, Γ') ⇒s Δ ,, Δ'
    σ +s τ = (λ x → [ var-inl ]ʳ (σ x)) ⋈s (λ y → [ var-inr ]ʳ (τ y))

    -- renaming as a substitution
    renaming-s : ∀ {Γ Δ} → Δ ⇒ʳ Γ → Θ ⊕ Γ ⇒s Δ
    renaming-s ρ x = tm-var (ρ x)

    -- extending a substitution
    extend-sˡ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒s Δ → Θ ⊕ (Γ ,, Ξ) ⇒s (Δ ,, Ξ)
    extend-sˡ σ = σ +s id-s

    extend-sʳ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒s Δ → Θ ⊕ Ξ ,, Γ ⇒s Ξ ,, Δ
    extend-sʳ σ = id-s +s σ

    -- the action of a substitution on a term (contravariant)
    infixr 6 _[_]s

    _[_]s : ∀ {Γ Δ : Context} {A : sort} → Term Θ Δ A → Θ ⊕ Γ ⇒s Δ → Term Θ Γ A
    (tm-var x) [ σ ]s = σ x
    (tm-meta M ts) [ σ ]s = tm-meta M (λ i → (ts i) [ σ ]s)
    (tm-oper f es) [ σ ]s = tm-oper f (λ i → es i [ extend-sˡ σ ]s)

    -- composition of substitutions

    infixl 7 _∘s_

    _∘s_ : ∀ {Γ Δ Ξ : Context} → Θ ⊕ Δ ⇒s Ξ → Θ ⊕ Γ ⇒s Δ → Θ ⊕ Γ ⇒s Ξ
    (σ ∘s ρ) x = σ x [ ρ ]s

    -- action of a substitution on a renaming
    _s∘ʳ_ : ∀ {Γ Δ Ξ} → Θ ⊕ Δ ⇒s Γ → Δ ⇒ʳ Ξ → Θ ⊕ Ξ ⇒s Γ
    σ s∘ʳ ρ = σ ∘s renaming-s ρ
