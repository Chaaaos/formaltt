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

  -- substitution

  infix 4 _⊕_⇒ˢ_

  _⊕_⇒ˢ_ : ∀ (Θ : MetaContext) (Γ Δ : Context) → Set (lsuc (ℓs ⊔ ℓo))
  Θ ⊕ Γ ⇒ˢ Δ = ∀ {A} (x : A ∈ Γ) → Term Θ Δ A

  -- identity substitution
  idˢ : ∀ {Θ Γ} → Θ ⊕ Γ ⇒ˢ Γ
  idˢ = tm-var

  module _ {Θ : MetaContext}  where

    -- the join of substitutions
    infixl 7 _⋈ˢ_

    _⋈ˢ_ : ∀ {Γ Δ Ψ} → Θ ⊕ Γ ⇒ˢ Ψ → Θ ⊕ Δ ⇒ˢ Ψ → Θ ⊕ Γ ,, Δ ⇒ˢ Ψ
    (σ ⋈ˢ τ) (var-inl x) = σ x
    (σ ⋈ˢ τ) (var-inr y) = τ y

    -- the sum of substitutions

    infixl 8 _+ˢ_

    _+ˢ_ : ∀ {Γ Γ' Δ Δ'} → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ Γ' ⇒ˢ Δ' → Θ ⊕ (Γ ,, Γ') ⇒ˢ Δ ,, Δ'
    σ +ˢ τ = (λ x → [ var-inl ]ʳ (σ x)) ⋈ˢ (λ y → [ var-inr ]ʳ (τ y))

    -- renaming as a substitution

    _ʳ⃗ˢ : ∀ {Γ Δ} → Γ ⇒ʳ Δ → Θ ⊕ Γ ⇒ˢ Δ
    (ρ ʳ⃗ˢ) x = tm-var (ρ x)

    -- extending a substitution

    ⇑ˢ : ∀ {Γ Δ Ψ} → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ (Γ ,, Ψ) ⇒ˢ (Δ ,, Ψ)
    ⇑ˢ σ = σ +ˢ idˢ

    -- the action of a substitution on a term (contravariant)
    infixr 6 [_]ˢ_

    [_]ˢ_ : ∀ {Γ Δ : Context} {A : sort} → Θ ⊕ Γ ⇒ˢ Δ → Term Θ Γ A → Term Θ Δ A
    [ σ ]ˢ (tm-var x) = σ x
    [ σ ]ˢ (tm-meta M ts) = tm-meta M (λ i → [ σ ]ˢ ts i)
    [ σ ]ˢ (tm-oper f es) = tm-oper f (λ i → [ ⇑ˢ σ ]ˢ es i)

    -- composition of substitutions

    infixl 7 _∘ˢ_

    _∘ˢ_ : ∀ {Γ Δ Ψ : Context} → Θ ⊕ Δ ⇒ˢ Ψ → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ Γ ⇒ˢ Ψ
    (σ ∘ˢ ρ) x = [ σ ]ˢ ρ x

    -- action of a substitution on a renaming
    _ˢ∘ʳ_ : ∀ {Γ Δ Ψ} → Θ ⊕ Δ ⇒ˢ Ψ → Γ ⇒ʳ Δ → Θ ⊕ Γ ⇒ˢ Ψ
    σ ˢ∘ʳ ρ = σ ∘ˢ ρ ʳ⃗ˢ

    -- syntactic equality of substitutions
    _≈ˢ_ : ∀ {Γ Δ} (σ τ : Θ ⊕ Γ ⇒ˢ Δ) → Set (lsuc (ℓs ⊔ ℓo))
    _≈ˢ_ {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≈ τ x
