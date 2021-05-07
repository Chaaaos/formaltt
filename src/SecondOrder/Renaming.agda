open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Term

module SecondOrder.Renaming
  {ℓs ℓo}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ

  -- a renaming is a morphism between contexts
  _⇒ʳ_ : ∀ (Γ Δ : Context) → Set ℓs
  Γ ⇒ʳ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

  infix 4 _⇒ʳ_

  -- renaming extension
  extendʳ : ∀ {Γ Δ} → Γ ⇒ʳ Δ → ∀ {Ξ} → Γ ,, Ξ ⇒ʳ Δ ,, Ξ
  extendʳ ρ (var-inl x) = var-inl (ρ x)
  extendʳ ρ (var-inr y) = var-inr y

  -- the identity renaming
  idʳ : ∀ {Γ : Context} → Γ ⇒ʳ Γ
  idʳ x = x

  -- composition of renamings
  _∘ʳ_ : ∀ {Γ Δ Ξ : Context} → Δ ⇒ʳ Ξ → Γ ⇒ʳ Δ → Γ ⇒ʳ Ξ
  (σ ∘ʳ ρ) x = σ (ρ x)

  infix 7 _∘ʳ_

  -- the reassociation renaming

  rename-assoc : ∀ {Γ Δ Ξ} → Γ ,, (Δ ,, Ξ) ⇒ʳ (Γ ,, Δ) ,, Ξ
  rename-assoc (var-inl x) = var-inl (var-inl x)
  rename-assoc (var-inr (var-inl y)) = var-inl (var-inr y)
  rename-assoc (var-inr (var-inr z)) = var-inr z

  -- the empty context is the unit

  rename-ctx-empty-r : ∀ {Γ} → Γ ,, ctx-empty ⇒ʳ Γ
  rename-ctx-empty-r (var-inl x) = x

  rename-ctx-empty-inv : ∀ {Γ} → Γ ⇒ʳ Γ ,, ctx-empty
  rename-ctx-empty-inv x = var-inl x

  module _ {Θ : MetaContext} where

    -- action of a renaming on terms
    [_]ʳ_ : ∀ {Γ Δ A} → Γ ⇒ʳ Δ → Term Θ Γ A → Term Θ Δ A
    [ ρ ]ʳ (tm-var x) = tm-var (ρ x)
    [ ρ ]ʳ (tm-meta M ts) = tm-meta M (λ i → [ ρ ]ʳ (ts i))
    [ ρ ]ʳ (tm-oper f es) = tm-oper f (λ i → [ (extendʳ ρ) ]ʳ (es i))

    infix 6 [_]ʳ_

    -- apply the reassociation renaming on terms
    term-reassoc : ∀ {Δ Γ Ξ A}
      → Term Θ (Δ ,, (Γ ,, Ξ)) A
      → Term Θ ((Δ ,, Γ) ,, Ξ) A
    term-reassoc = [ rename-assoc ]ʳ_

    -- weakening
    ⇑ʳ : ∀ {Γ Δ A} → Term Θ Γ A → Term Θ (Γ ,, Δ) A
    ⇑ʳ = [ var-inl ]ʳ_
