-- {-# OPTIONS --allow-unsolved-metas #-}

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



-- ** DEFINITIONS **

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

  -- the injection renamings
  inlʳ : ∀ {Γ Δ} → Γ ⇒ʳ Γ ,, Δ
  inlʳ = var-inl

  inrʳ : ∀ {Γ Δ} → Δ ⇒ʳ Γ ,, Δ
  inrʳ = var-inr

  -- composition of renamings
  _∘ʳ_ : ∀ {Γ Δ Ξ : Context} → Δ ⇒ʳ Ξ → Γ ⇒ʳ Δ → Γ ⇒ʳ Ξ
  (σ ∘ʳ ρ) x = σ (ρ x)

  infix 7 _∘ʳ_

  -- the reassociation renaming
  rename-assoc : ∀ {Γ Δ Ξ} → Γ ,, (Δ ,, Ξ) ⇒ʳ (Γ ,, Δ) ,, Ξ
  rename-assoc (var-inl x) = var-inl (var-inl x)
  rename-assoc (var-inr (var-inl y)) = var-inl (var-inr y)
  rename-assoc (var-inr (var-inr z)) = var-inr z

  -- the inverse of the reassociation renaming
  rename-unassoc : ∀ {Γ Δ Ξ} → (Γ ,, Δ) ,, Ξ ⇒ʳ Γ ,, (Δ ,, Ξ)
  rename-unassoc (var-inl (var-inl x)) = var-inl x
  rename-unassoc (var-inl (var-inr x)) = var-inr (var-inl x)
  rename-unassoc (var-inr x) = var-inr (var-inr x)

  -- the empty context is the right unit

  ctx-empty-right-unit : ∀ {Γ} → Γ ,, ctx-empty ⇒ʳ Γ
  ctx-empty-right-unit (var-inl x) = x

  rename-ctx-empty-inv : ∀ {Γ} → Γ ⇒ʳ Γ ,, ctx-empty
  rename-ctx-empty-inv x = var-inl x

  -- the empty context is the left unit

  ctx-empty-left-unit : ∀ {Γ} → ctx-empty ,, Γ ⇒ʳ Γ
  ctx-empty-left-unit (var-inr x) = x


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


  -- the join of renamings
  infixl 7 _⋈ʳ_

  _⋈ʳ_ : ∀ {Γ Δ Ξ} → Γ ⇒ʳ Ξ → Δ ⇒ʳ Ξ → Γ ,, Δ ⇒ʳ Ξ
  (σ ⋈ʳ τ) (var-inl x) = σ x
  (σ ⋈ʳ τ) (var-inr y) = τ y

  -- the sum of renamings
  infixl 8 _+ʳ_
  _+ʳ_ : ∀ {Γ Γ' Δ Δ'} → Γ ⇒ʳ Δ → Γ' ⇒ʳ Δ' → (Γ ,, Γ') ⇒ʳ Δ ,, Δ'
  σ +ʳ τ = (λ x → var-inl (σ x)) ⋈ʳ (λ y → var-inr (τ y))

  -- equality of renamings
  _≡ʳ_ : ∀ {Γ Δ} (σ τ : Γ ⇒ʳ Δ) → Set ℓs
  _≡ʳ_ {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≡ τ x

  infixl 3 _≡ʳ_


--========================================================================================
--∥                              ========================                                ∥
--∥                              ∥  ** METATHEOREMS **  ∥                                ∥
--∥                              ========================                                ∥
--========================================================================================

  -------------------------------------------
  --          Lemmas about sums           --
  -------------------------------------------

  -- We want to show that sums of renamings form a coproduct of morphisms
  -- in the category where Contexts are the objects and renamings the morphisms
  -- between them.

  -- The join of two renamings gives us the renaming prophesied by the
  -- universal property of coproducts.
  -- Now we just need to show uniqueness:
  unique⋈ : ∀ {Γ Δ Ξ} {σ : Γ ⇒ʳ Ξ} {ν : Δ ⇒ʳ Ξ} {δ : Γ ,, Δ ⇒ʳ Ξ}
          → (δ ∘ʳ inlʳ) ≡ʳ σ
          → (δ ∘ʳ inrʳ) ≡ʳ ν
          → δ ≡ʳ (σ ⋈ʳ ν)
  unique⋈ eq1 eq2 (var-inl x) = eq1 x
  unique⋈ eq1 eq2 (var-inr y) = eq2 y

  -- We have existance of coproducts of renamings with the sum
  -- once again, what about uniqueness?
  -- For any renaming ρ : Γ ,, Γ' → Δ ,, Δ' that makes the corresponding
  -- squares commute, we have ρ ≡ʳ σ +ʳ τ
  unique+ : ∀ {Γ Γ' Δ Δ' Ξ Λ} {ρ : Γ ⇒ʳ Δ} {ν : Γ' ⇒ʳ Δ'} {δ : Ξ ⇒ʳ Λ}
    → (α₁ : Γ ⇒ʳ Ξ) → (α₂ : Δ ⇒ʳ Λ) → (δ ∘ʳ α₁) ≡ʳ (α₂ ∘ʳ ρ)
    → (β₁ : Γ' ⇒ʳ Ξ) → (β₂ : Δ' ⇒ʳ Λ) → (δ ∘ʳ β₁) ≡ʳ (β₂ ∘ʳ ν)
    → δ ∘ʳ (α₁ ⋈ʳ β₁) ≡ʳ (α₂ ⋈ʳ β₂) ∘ʳ (ρ +ʳ ν)
  unique+ α₁ α₂ eq1 β₁ β₂ eq2 (var-inl x) = eq1 x
  unique+ α₁ α₂ eq1 β₁ β₂ eq2 (var-inr y) = eq2 y

  -- Lemma: The extension of a renaming is equal to summing with the identity renaming
  extendʳ≡+id : ∀ {Γ Δ Ξ} {ρ : Γ ⇒ʳ Δ}
             → (extendʳ ρ {Ξ}) ≡ʳ (ρ +ʳ idʳ)
  extendʳ≡+id (var-inl x) = refl
  extendʳ≡+id (var-inr y) = refl

  -- Lemma: The sum of two equal renamings is equal
  ≡ʳ+ʳ : ∀ {Γ Δ Ξ Λ} {ρ ρ' : Γ ⇒ʳ Δ} {ν ν' : Ξ ⇒ʳ Λ}
       → ρ ≡ʳ ρ' → ν ≡ʳ ν'
       → (ρ +ʳ ν) ≡ʳ (ρ' +ʳ ν')
  ≡ʳ+ʳ eq1 eq2 (var-inl x) = cong var-inl (eq1 x)
  ≡ʳ+ʳ eq1 eq2 (var-inr y) = cong var-inr (eq2 y)

  -- (1) the extension of to equal renamings are equal
  ≡ʳextendʳ : ∀ {Γ Δ Ξ} {ρ ν : Γ ⇒ʳ Δ}
        → ρ ≡ʳ ν → extendʳ ρ {Ξ = Ξ} ≡ʳ extendʳ ν
  ≡ʳextendʳ p (var-inl x) = ≡-inl (p x)
  ≡ʳextendʳ p (var-inr x) = refl

  -- (2) two equal renamings have the same action
  ≈ʳ[]ʳ : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {ρ ν : Γ ⇒ʳ Δ}
        → ρ ≡ʳ ν → [ ρ ]ʳ t ≈ [ ν ]ʳ t
  ≈ʳ[]ʳ {t = tm-var x} p = ≈-≡ (≡-var (p x))
  ≈ʳ[]ʳ {t = tm-meta M ts} p = ≈-meta λ i → ≈ʳ[]ʳ p
  ≈ʳ[]ʳ {Θ} {A = A} {t = tm-oper f es} p = ≈-oper (λ i → ≈ʳ[]ʳ (≡ʳextendʳ p))

  -- (3) the extension of a composition is equal to the composition of extensions
  ∘r-≈-extendʳ : ∀ {Γ Δ Λ Ξ} (ρ : Γ ⇒ʳ Δ) (ν : Δ ⇒ʳ Λ)
        →  extendʳ (ν ∘ʳ ρ) {Ξ = Ξ} ≡ʳ ((extendʳ ν) ∘ʳ (extendʳ ρ))
  ∘r-≈-extendʳ ρ ν (var-inl x) = refl
  ∘r-≈-extendʳ ρ ν (var-inr x) = refl

  -- (4) composition of renamings commutes with equality
  ∘r-≈ : ∀ {Θ Γ Δ Ξ A} (t : Term Θ Γ A) (ρ : Γ ⇒ʳ Δ) (ν : Δ ⇒ʳ Ξ)
        → [ ν ∘ʳ ρ ]ʳ t ≈ [ ν ]ʳ ([ ρ ]ʳ t)
  ∘r-≈ (tm-var x) ρ ν = ≈-≡ refl
  ∘r-≈ (tm-meta M ts) ρ ν = ≈-meta (λ i → ∘r-≈ (ts i) ρ ν)
  ∘r-≈ (tm-oper f es) ρ ν = ≈-oper λ i → ≈-trans
                                           (≈ʳ[]ʳ (∘r-≈-extendʳ ρ ν))
                                           (∘r-≈ (es i) (extendʳ ρ) (extendʳ ν))


  -- (5) the action of the identity renaming is the identity
  -- auxiliary function for (5), to deal with extensions in the oper case
  -- the extension of the identity is the identity
  idʳextendʳ : ∀ {Γ Ξ} → extendʳ (idʳ {Γ = Γ})  {Ξ = Ξ}  ≡ʳ idʳ
  idʳextendʳ (var-inl x) = refl
  idʳextendʳ (var-inr x) = refl

  -- (5)
  []ʳidʳ : ∀ {Θ Γ A} (t : Term Θ Γ A)
          → [ idʳ ]ʳ t ≈ t
  []ʳidʳ (tm-var x) = ≈-≡ refl
  []ʳidʳ (tm-meta M ts) = ≈-meta λ i → []ʳidʳ (ts i)
  []ʳidʳ (tm-oper f es) = ≈-oper λ i → ≈-trans
                                       (≈ʳ[]ʳ idʳextendʳ)
                                       ([]ʳidʳ (es i))

  -- (6) renamings preserve syntactical equality of terms
  ≈-tm-ʳ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Γ ⇒ʳ Δ}
        → s ≈ t → [ ρ ]ʳ s ≈ [ ρ ]ʳ t
  ≈-tm-ʳ (≈-≡ refl) = ≈-≡ refl
  ≈-tm-ʳ (≈-meta ξ) = ≈-meta (λ i → ≈-tm-ʳ (ξ i))
  ≈-tm-ʳ (≈-oper ξ) = ≈-oper (λ i → ≈-tm-ʳ (ξ i))


  -- the reassociation renaming and "unassociation" renaming are inverse
  unassoc-reassoc : ∀ {Γ Δ Ξ} → (rename-unassoc {Δ} {Γ} {Ξ}) ∘ʳ rename-assoc ≡ʳ idʳ
  unassoc-reassoc (var-inl x) = refl
  unassoc-reassoc (var-inr (var-inl x)) = refl
  unassoc-reassoc (var-inr (var-inr x)) = refl

  -- "reassociating" and then "unassociating" a term acts like the identity

  unassoc-reassoc-tm : ∀ {Θ Γ Δ Ξ A} (t : Term Θ (Γ ,, (Δ ,, Ξ)) A) → [ rename-unassoc ]ʳ (term-reassoc t) ≈ t
  unassoc-reassoc-tm t = ≈-trans
                           (≈-trans
                             (≈-sym (∘r-≈ t rename-assoc rename-unassoc))
                             (≈ʳ[]ʳ unassoc-reassoc))
                           ([]ʳidʳ t)

  -- term-reassociation preserves syntactical equality of terms
  ≈-tm-reassoc : ∀ {Θ Γ Δ Ξ A} {s t : Term Θ (Γ ,, (Δ ,, Ξ)) A}
                 → term-reassoc s ≈ term-reassoc t → s ≈ t
  ≈-tm-reassoc {s = s} {t = t} p = ≈-trans
                                     (≈-sym (unassoc-reassoc-tm s))
                                     (≈-sym (≈-trans
                                       (≈-sym (unassoc-reassoc-tm t))
                                       (≈-tm-ʳ (≈-sym p))))

  -- extending two times is like extending one time and reassociating
  extendʳ² : ∀ {Γ Δ Ξ Λ Ω} (ρ : Γ ,, Δ ⇒ʳ Ω)
             → (rename-unassoc {Δ = Ξ} {Ξ = Λ}) ∘ʳ (extendʳ  (extendʳ ρ)) ≡ʳ (extendʳ ρ) ∘ʳ rename-unassoc
  extendʳ² ρ (var-inl (var-inl x)) = refl
  extendʳ² ρ (var-inl (var-inr x)) = refl
  extendʳ² ρ (var-inr x) = refl
