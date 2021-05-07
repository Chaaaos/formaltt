open import Agda.Primitive using (lzero; lsuc; _⊔_)

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

  -- metavariable instantiation
  _⇒ⁱ_⊕_  : MetaContext → MetaContext → Context → Set (lsuc (ℓs ⊔ ℓo))
  ψ ⇒ⁱ Θ ⊕ Γ = ∀ (M : mv Θ) → Term ψ (Γ ,, mv-arity Θ M) (mv-sort Θ M)

  -- the identity metavariable instantiation
  idⁱ : ∀ {Θ} → Θ ⇒ⁱ Θ ⊕ ctx-empty
  idⁱ t = tm-meta t (λ i → [ var-inr ]ʳ (tm-var i))

  -- action of a metavariable instantiation on terms

  infixr 6 [_]ⁱ_

  [_]ⁱ_ : ∀ {Θ Ψ Γ Δ A} → Ψ ⇒ⁱ Θ ⊕ Δ → Term Θ Γ A → Term Ψ (Δ ,, Γ) A
  [ I ]ⁱ (tm-var x) = tm-var (var-inr x)
  [ I ]ⁱ (tm-meta M ts) = I M [ var-inl ʳ⃗ˢ ⋈ˢ (λ x →  [ I ]ⁱ ts x) ]ˢ
  [ I ]ⁱ (tm-oper f es) = tm-oper f λ i → term-reassoc ([ I ]ⁱ es i)

  -- idⁱ-inv : ∀ {Θ Γ} → (ctx-empty ,, Γ) ⇒ʳ Γ
  -- idⁱ-inv (var-inr x) = x

  -- composition of metavariable instantiations
  infixl 5 _∘ⁱ_

  _∘ⁱ_ : ∀ {Θ ψ Ω Γ Δ} → Ω ⇒ⁱ ψ ⊕ Δ → ψ ⇒ⁱ Θ ⊕ Γ → (Ω ⇒ⁱ Θ ⊕ (Δ ,, Γ))
  (I ∘ⁱ J) M =  term-reassoc ([ I ]ⁱ (J M))
