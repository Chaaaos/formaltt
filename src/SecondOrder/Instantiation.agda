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
  _⇒i_⊕_  : MetaContext → MetaContext → Context → Set (lsuc (ℓs ⊔ ℓo))
  ψ ⇒i Θ ⊕ Γ = ∀ (M : mv Θ) → Term ψ (Γ ,, mv-arity Θ M) (mv-sort Θ M)

  -- the identity metavariable instantiation
  id-i : ∀ {Θ} → Θ ⇒i Θ ⊕ ctx-empty
  id-i t = tm-meta t (λ i → weakenʳ (tm-var i))

  -- action of a metavariable instantiation on terms

  infixr 6 [_]i_

  [_]i_ : ∀ {Θ Ψ Γ Δ A} → Ψ ⇒i Θ ⊕ Δ → Term Θ Γ A → Term Ψ (Δ ,, Γ) A
  [ I ]i (tm-var x) = tm-var (var-inr x)
  [ I ]i (tm-meta M ts) = I M [ (renaming-s var-inl) ⋈s (λ x →  [ I ]i ts x) ]s
  [ I ]i (tm-oper f es) = tm-oper f λ i → term-reassoc ([ I ]i es i)

  -- id-i-inv : ∀ {Θ Γ} → (ctx-empty ,, Γ) ⇒r Γ
  -- id-i-inv (var-inr x) = x

  -- composition of metavariable instantiations
  infixl 5 _∘i_

  _∘i_ : ∀ {Θ ψ Ω Γ Δ} → Ω ⇒i ψ ⊕ Δ → ψ ⇒i Θ ⊕ Γ → (Ω ⇒i Θ ⊕ (Δ ,, Γ))
  (I ∘i J) M =  term-reassoc ([ I ]i (J M))
