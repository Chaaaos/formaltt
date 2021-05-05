open import Agda.Primitive using (lzero; lsuc; _⊔_)

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
  _⇒r_ : ∀ (Γ Δ : Context) → Set ℓs
  Γ ⇒r Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

  infix 4 _⇒r_

  -- renaming extension
  extend-r : ∀ {Γ Δ} → Γ ⇒r Δ → ∀ {Ξ} → Γ ,, Ξ ⇒r Δ ,, Ξ
  extend-r ρ (var-inl x) = var-inl (ρ x)
  extend-r ρ (var-inr y) = var-inr y

  -- the identity renaming
  id-r : ∀ {Γ : Context} → Γ ⇒r Γ
  id-r x = x

  -- composition of renamings
  _∘r_ : ∀ {Γ Δ Ξ : Context} → Δ ⇒r Ξ → Γ ⇒r Δ → Γ ⇒r Ξ
  (σ ∘r ρ) x = σ (ρ x)

  infix 7 _∘r_

  -- the reassociation renaming

  rename-assoc : ∀ {Γ Δ Ξ} → Γ ,, (Δ ,, Ξ) ⇒r (Γ ,, Δ) ,, Ξ
  rename-assoc (var-inl x) = var-inl (var-inl x)
  rename-assoc (var-inr (var-inl y)) = var-inl (var-inr y)
  rename-assoc (var-inr (var-inr z)) = var-inr z

  -- the empty context is the unit

  rename-ctx-empty-r : ∀ {Γ} → Γ ,, ctx-empty ⇒r Γ
  rename-ctx-empty-r (var-inl x) = x

  rename-ctx-empty-inv : ∀ {Γ} → Γ ⇒r Γ ,, ctx-empty
  rename-ctx-empty-inv x = var-inl x

  module _ {Θ : MetaContext} where

    -- action of a renaming on terms
    [_]r_ : ∀ {Γ Δ A} → Γ ⇒r Δ → Term Θ Γ A → Term Θ Δ A
    [ ρ ]r (tm-var x) = tm-var (ρ x)
    [ ρ ]r (tm-meta M ts) = tm-meta M (λ i → [ ρ ]r (ts i))
    [ ρ ]r (tm-oper f es) = tm-oper f (λ i → [ (extend-r ρ) ]r (es i))

    infix 6 [_]r_

    -- apply the reassociation renaming on terms
    term-reassoc : ∀ {Δ Γ Ξ A}
      → Term Θ (Δ ,, (Γ ,, Ξ)) A
      → Term Θ ((Δ ,, Γ) ,, Ξ) A
    term-reassoc = [ rename-assoc ]r_

    -- weakening
    weakenˡ : ∀ {Γ Δ A} → Term Θ Γ A → Term Θ (Γ ,, Δ) A
    weakenˡ = [ var-inl ]r_

    weakenʳ : ∀ {Γ Δ A} → Term Θ Δ A → Term Θ (Γ ,, Δ) A
    weakenʳ = [ var-inr ]r_

    -- this is probably useless to have a name for
    -- but it allows us to use the extended renaming as a fuction from terms to terms
    app-extend-r : ∀ {Γ Δ Ξ A} → Γ ⇒r Δ → Term Θ (Γ ,, Ξ) A → Term Θ (Δ ,, Ξ) A
    app-extend-r ρ t = [ extend-r ρ ]r t
