open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Renaming
import SecondOrder.Term
import SecondOrder.Substitution

module SecondOrder.Instantiation
  {ℓs ℓo}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.Renaming Σ
  open SecondOrder.Substitution Σ


-- ** DEFINITIONS **

  -- metavariable instantiation
  _⇒ⁱ_⊕_  : MetaContext → MetaContext → Context → Set (lsuc (ℓs ⊔ ℓo))
  Θ ⇒ⁱ Ξ ⊕ Γ = ∀ (M : mv Θ) → Term Ξ (Γ ,, mv-arity Θ M) (mv-sort Θ M)

  -- the identity metavariable instantiation
  idⁱ : ∀ {Θ} → Θ ⇒ⁱ Θ ⊕ ctx-empty
  idⁱ t = tm-meta t (λ i → [ var-inr ]ʳ (tm-var i))

  -- action of a metavariable instantiation on terms

  infixr 6 [_]ⁱ_

  [_]ⁱ_ : ∀ {Θ Ξ Γ Δ A} → Ξ ⇒ⁱ Θ ⊕ Δ → Term Ξ Γ A → Term Θ (Δ ,, Γ) A
  [ I ]ⁱ (tm-var x) = tm-var (var-inr x)
  [ I ]ⁱ (tm-meta M ts) = [ var-inl ʳ⃗ˢ ⋈ˢ (λ x →  [ I ]ⁱ ts x) ]ˢ I M
  [ I ]ⁱ (tm-oper f es) = tm-oper f λ i → term-reassoc ([ I ]ⁱ es i)

  -- idⁱ-inv : ∀ {Θ Γ} → (ctx-empty ,, Γ) ⇒ʳ Γ
  -- idⁱ-inv (var-inr x) = x

  -- composition of metavariable instantiations
  infixl 5 _∘ⁱ_

  _∘ⁱ_ : ∀ {Θ Ξ Ω Γ Δ} → Ξ ⇒ⁱ Ω ⊕ Δ → Θ ⇒ⁱ Ξ ⊕ Γ → (Θ ⇒ⁱ Ω ⊕ (Δ ,, Γ))
  (I ∘ⁱ J) M =  term-reassoc ([ I ]ⁱ (J M))

  -- syntactic equality of instantiations
  _≈ⁱ_ : ∀ {Θ Ξ Γ} (I J : Θ ⇒ⁱ Ξ ⊕ Γ) → Set (lsuc (ℓs ⊔ ℓo))
  _≈ⁱ_ {Θ} I J = ∀ (M : mv Θ) → I M ≈ J M

  -- as a special case we define instantiation of a closed term such that
  -- the empty context does not appear. This is used when axioms are instantiated.

  instantiate-closed-term : ∀ {Θ Ξ Γ A} (I : Θ ⇒ⁱ Ξ ⊕ Γ) → Term Θ ctx-empty A → Term Ξ Γ A
  instantiate-closed-term I t =  [ ctx-empty-right-unit ]ʳ ([ I ]ⁱ t)


-- ** METATHEOREMS **

  -- two equal instantiations have the same action
  ≈ⁱ[]ⁱ : ∀ {Θ Ω Γ Δ A} {t : Term Θ Δ A} {σ τ : Θ ⇒ⁱ Ω ⊕ Γ}
        → σ ≈ⁱ τ → [ σ ]ⁱ t ≈ [ τ ]ⁱ t
  ≈ⁱ[]ⁱ {t = tm-var x} p = ≈-≡ refl
  ≈ⁱ[]ⁱ {t = tm-meta M ts} p = {!!} -- ≈-meta λ i → ≈ˢ[]ˢ {t = ts i} p
  ≈ⁱ[]ⁱ {t = tm-oper f es} p = ≈-oper λ i → ≈-tm-ʳ (≈ⁱ[]ⁱ {t = es i} p)

  -- composition of substitutions commutes with equality
  ∘ⁱ-≈ : ∀ {Θ Ω ψ Γ Δ Ξ A} (t : Term Θ Ξ A) (σ : Θ ⇒ⁱ Ω ⊕ Γ) (τ : Ω ⇒ⁱ ψ ⊕ Δ)
        → [ τ ∘ⁱ σ ]ⁱ t ≈ term-reassoc ([ τ ]ⁱ ([ σ ]ⁱ t))
  ∘ⁱ-≈ (tm-var x) σ τ = ≈-≡ refl
  ∘ⁱ-≈ (tm-meta M ts) σ τ = {!!} -- ≈-meta (λ i → ∘ˢ-≈ (ts i) σ τ)
  ∘ⁱ-≈ (tm-oper f es) σ τ = ≈-oper λ i → {!!}

  -- the action of the identity instantiation is the identity
  []ⁱidⁱ : ∀ {Θ Γ A} (t : Term Θ Γ A)
           → [ ctx-empty-left-unit ]ʳ ([ idⁱ ]ⁱ t) ≈ t
  []ⁱidⁱ (tm-var x) = ≈-≡ refl
  []ⁱidⁱ (tm-meta M ts) = {!!} -- ≈-meta λ i → []ˢidˢ (ts i)
  []ⁱidⁱ (tm-oper f es) = ≈-oper λ i → {!!} -- ≈-oper λ i → ≈-trans
                                         -- (≈ˢ[]ˢ {t = es i} idˢextendˢ)
                                         -- ([]ˢidˢ (es i))

  -- substitutions preserve syntactical equality of terms
  ≈-tm-ⁱ : ∀ {Θ Ω Γ Δ A} {s t : Term Θ Δ A} {σ : Θ ⇒ⁱ Ω ⊕ Γ}
        → s ≈ t → [ σ ]ⁱ s ≈ [ σ ]ⁱ t
  ≈-tm-ⁱ (≈-≡ refl) = ≈-≡ refl
  ≈-tm-ⁱ {t = tm-meta M ts} {σ = σ} (≈-meta ξ) = ≈ˢ[]ˢ {t = σ M} {!!}
  ≈-tm-ⁱ (≈-oper ξ) = ≈-oper λ i → ≈-tm-ʳ (≈-tm-ⁱ (ξ i))
