open import Agda.Primitive using (lzero; lsuc; _⊔_)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable

module SecondOrder.Term
  ℓs ℓo
  (𝔸 : SecondOrder.Arity.Arity)
  (Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸)
  where

  open SecondOrder.Metavariable ℓs ℓo 𝔸 Σ
  open SecondOrder.Signature.Signature Σ

  -- The term judgement
  data Term (Θ : MetaContext) : ∀ (Γ : Context) (A : sort) → Set (lsuc (ℓs ⊔ ℓo)) where
    tm-var : ∀ {Γ} {A} (x : A ∈ Γ) → Term Θ Γ A
    tm-meta : ∀ {Γ} (M : mv Θ)
                (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)
                → Term Θ Γ (mv-sort Θ M)
    tm-oper : ∀ {Γ} (f : oper)
                (es : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i))
                → Term Θ Γ (oper-sort f)
