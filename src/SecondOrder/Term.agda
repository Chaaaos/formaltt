open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable

module SecondOrder.Term
  {ℓs ℓo}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ

  -- The term judgement
  data Term (Θ : MetaContext) : ∀ (Γ : Context) (A : sort) → Set (lsuc (ℓs ⊔ ℓo)) where
    tm-var : ∀ {Γ} {A} (x : A ∈ Γ) → Term Θ Γ A
    tm-meta : ∀ {Γ} (M : mv Θ)
                (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)
                → Term Θ Γ (mv-sort Θ M)
    tm-oper : ∀ {Γ} (f : oper)
                (es : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i))
                → Term Θ Γ (oper-sort f)

  -- Special cases of function extensionality

  postulate tm-eq-meta : ∀ {Θ Γ} {M : mv Θ} {ts us : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B} →
                         (∀ {B} i → ts {B} i ≡ us {B} i) → tm-meta M ts ≡ tm-meta M us

  postulate tm-eq-oper : ∀ {Θ Γ} {f : oper} {ds es : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i)} →
                         (∀ i → ds i ≡ es i) → tm-oper f ds ≡ tm-oper f es
