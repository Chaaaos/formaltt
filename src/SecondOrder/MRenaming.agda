open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)
import Function.Equality
import Relation.Binary.Reasoning.Setoid as SetoidR

import Categories.Category
import Categories.Functor
import Categories.NaturalTransformation
import Categories.Category.Instance.Setoids

import Categories.Category.Cocartesian

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Term
import SecondOrder.VRenaming

module SecondOrder.MRenaming
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.VRenaming Σ

  -- a metarenaming maps metavariables between contexts in an arity-preserving way
  _⇒ᵐ_ : ∀ (Θ ψ : MContext) → Set ℓ
  Θ ⇒ᵐ ψ = ∀ {Δ A} → [ Δ , A ]∈ Θ → [ Δ , A ]∈ ψ

  infix 4 _⇒ᵐ_

  -- equality of metarenamings

  _≡ᵐ_ : ∀ {Θ ψ} (ι μ : Θ ⇒ᵐ ψ) → Set ℓ
  _≡ᵐ_ {Θ} ι μ = ∀ {Δ A} (M : [ Δ , A ]∈ Θ) → ι M ≡ μ M

  infixl 3 _≡ᵐ_

  ≡ᵐ-refl : ∀ {Θ ψ} {ι : Θ ⇒ᵐ ψ} → ι ≡ᵐ ι
  ≡ᵐ-refl = λ M → refl

  ≡ᵐ-sym : ∀ {Θ ψ} {ι μ : Θ ⇒ᵐ ψ}
          → ι ≡ᵐ μ
          → μ ≡ᵐ ι
  ≡ᵐ-sym eq M = sym (eq M)

  ≡ᵐ-trans : ∀ {Θ ψ} {ι μ δ : Θ ⇒ᵐ ψ}
           → ι ≡ᵐ μ
           → μ ≡ᵐ δ
           → ι ≡ᵐ δ
  ≡ᵐ-trans eq1 eq2 M = trans (eq1 M) (eq2 M)

  -- meta-variable renamings form a setoid

  Mrenaming-setoid : ∀ (Θ ψ : MContext) → Setoid ℓ ℓ
  Mrenaming-setoid Θ ψ =
    record
      { Carrier = Θ ⇒ᵐ ψ
      ;  _≈_ = λ ι μ → ι ≡ᵐ μ
      ; isEquivalence =
                      record
                        { refl = λ {ι} M → ≡ᵐ-refl {Θ} {ψ} {ι} M
                        ; sym = ≡ᵐ-sym
                        ; trans = ≡ᵐ-trans
                        }
      }

  -- the identity renaming

  idᵐ : ∀ {Θ : MContext} → Θ ⇒ᵐ Θ
  idᵐ M = M

  -- equal metavariable renaming act the same on metavariables


  -- composition of renamings
  _∘ᵐ_ : ∀ {Θ ψ Ω} → ψ ⇒ᵐ Ω → Θ ⇒ᵐ ψ → Θ ⇒ᵐ Ω
  (ι ∘ᵐ μ) M = ι (μ M)

  infix 7 _∘ᵐ_

  -- composition respects equality
  ∘ᵐ-resp-≡ᵐ : ∀ {Γ Δ Ξ} {τ₁ τ₂ : Δ ⇒ᵐ Ξ} {σ₁ σ₂ : Γ ⇒ᵐ Δ} →
                 τ₁ ≡ᵐ τ₂ → σ₁ ≡ᵐ σ₂ → τ₁ ∘ᵐ σ₁ ≡ᵐ τ₂ ∘ᵐ σ₂
  ∘ᵐ-resp-≡ᵐ {τ₁ = τ₁} {σ₂ = σ₂} ζ ξ x = trans (cong τ₁ (ξ x)) (ζ (σ₂ x))

  -- the identity is the unit

  identity-leftᵐ : ∀ {Γ Δ} {ρ : Γ ⇒ᵐ Δ} → idᵐ ∘ᵐ ρ ≡ᵐ ρ
  identity-leftᵐ ρ = refl

  identity-rightᵐ : ∀ {Γ Δ} {ρ : Γ ⇒ᵐ Δ} → ρ ∘ᵐ idᵐ ≡ᵐ ρ
  identity-rightᵐ ρ = refl

  -- composition is associative

  assocᵐ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ᵐ Δ} {ρ : Δ ⇒ᵐ Ξ} {σ : Ξ ⇒ᵐ Ψ} →
             (σ ∘ᵐ ρ) ∘ᵐ τ ≡ᵐ σ ∘ᵐ (ρ ∘ᵐ τ)
  assocᵐ x = refl

  sym-assocᵐ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ᵐ Δ} {ρ : Δ ⇒ᵐ Ξ} {σ : Ξ ⇒ᵐ Ψ} →
             σ ∘ᵐ (ρ ∘ᵐ τ) ≡ᵐ (σ ∘ᵐ ρ) ∘ᵐ τ
  sym-assocᵐ x = refl

  -- contexts and renamings form a category
  module _ where
    open Categories.Category

    MContexts : Category ℓ ℓ ℓ
    MContexts =
      record
        { Obj = MContext
        ; _⇒_ = _⇒ᵐ_
        ; _≈_ = _≡ᵐ_
        ; id = idᵐ
        ; _∘_ = _∘ᵐ_
        ; assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → assocᵐ {τ = f} {ρ = g} {σ = h}
        ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → sym-assocᵐ {τ = f} {ρ = g} {σ = h}
        ; identityˡ = λ x → refl
        ; identityʳ = λ x → refl
        ; identity² = λ x → refl
        ; equiv = record { refl = λ {ι} {_} → ≡ᵐ-refl {ι = ι} ; sym = ≡ᵐ-sym ; trans = ≡ᵐ-trans }
        ; ∘-resp-≈ = ∘ᵐ-resp-≡ᵐ
        }


  -- the coproduct structure of the category
  module _ where

    infixl 7 [_,_]ᵐ

    [_,_]ᵐ : ∀ {Γ Δ Ξ} → Γ ⇒ᵐ Ξ → Δ ⇒ᵐ Ξ → Γ ,, Δ ⇒ᵐ Ξ
    [ σ , τ ]ᵐ (var-inl x) = σ x
    [ σ , τ ]ᵐ (var-inr y) = τ y

    inlᵐ : ∀ {Γ Δ} → Γ ⇒ᵐ Γ ,, Δ
    inlᵐ = var-inl

    inrᵐ : ∀ {Γ Δ} → Δ ⇒ᵐ Γ ,, Δ
    inrᵐ = var-inr

    uniqueᵐ : ∀ {Γ Δ Ξ} {τ : Γ ,, Δ ⇒ᵐ Ξ} {ρ : Γ ⇒ᵐ Ξ} {σ : Δ ⇒ᵐ Ξ}
              → τ ∘ᵐ inlᵐ ≡ᵐ ρ
              → τ ∘ᵐ inrᵐ ≡ᵐ σ
              → [ ρ , σ ]ᵐ ≡ᵐ τ
    uniqueᵐ ξ ζ (var-inl x) = sym (ξ x)
    uniqueᵐ ξ ζ (var-inr y) = sym (ζ y)

    MContext-+ : Categories.Category.Cocartesian.BinaryCoproducts MContexts
    MContext-+ =
      record {
        coproduct =
          λ {Γ Δ} →
          record
            { A+B = Γ ,, Δ
            ; i₁ = inlᵐ
            ; i₂ = inrᵐ
            ; [_,_] = [_,_]ᵐ
            ; inject₁ = λ x → refl
            ; inject₂ = λ x → refl
            ; unique = uniqueᵐ
            }
      }

  open Categories.Category.Cocartesian.BinaryCoproducts MContext-+

  -- the renaming from the empty context

  inᵐ : ∀ {Γ} → ctx-empty ⇒ᵐ Γ
  inᵐ ()

  -- extension of a renaming is summing with identity
  ⇑ᵐ : ∀ {Θ Ψ Ω} → Θ ⇒ᵐ Ψ → Θ ,, Ω ⇒ᵐ Ψ ,, Ω
  ⇑ᵐ ρ = ρ +₁ idᵐ

  -- a renaming can also be extended on the right
  ᵐ⇑ᵐ : ∀ {Θ Ψ} → Θ ⇒ᵐ Ψ → ∀ {Ω} → Ω ,, Θ ⇒ᵐ Ω ,, Ψ
  ᵐ⇑ᵐ ρ = idᵐ +₁ ρ


  -- the action of a metavariable renaming on terms
  infix 6 [_]ᵐ_

  [_]ᵐ_ : ∀ {Θ Ψ Γ A} → Θ ⇒ᵐ Ψ → Term Θ Γ A → Term Ψ Γ A
  [ ι ]ᵐ (tm-var x) = tm-var x
  [ ι ]ᵐ (tm-meta M ts) = tm-meta (ι M) (λ i → [ ι ]ᵐ ts i)
  [ ι ]ᵐ (tm-oper f es) = tm-oper f (λ i → [ ι ]ᵐ es i)

  -- The sum of identities is an identity
  idᵐ+idᵐ : ∀ {Θ Ψ} → idᵐ {Θ = Θ} +₁ idᵐ {Θ = Ψ} ≡ᵐ idᵐ {Θ = Θ ,, Ψ}
  idᵐ+idᵐ (var-inl x) = refl
  idᵐ+idᵐ (var-inr y) = refl

  -- The action of a renaming respects equality of terms
  []ᵐ-resp-≈ : ∀ {Θ Ψ Γ A} {s t : Term Θ Γ A} {ι : Θ ⇒ᵐ Ψ} → s ≈ t → [ ι ]ᵐ s ≈ [ ι ]ᵐ t
  []ᵐ-resp-≈ (≈-≡ refl) = ≈-≡ refl
  []ᵐ-resp-≈ (≈-meta ξ) = ≈-meta (λ i → []ᵐ-resp-≈ (ξ i))
  []ᵐ-resp-≈ (≈-oper ξ) = ≈-oper (λ i → []ᵐ-resp-≈ (ξ i))

  -- The action of a renaming respects equality of renamings
  []ᵐ-resp-≡ᵐ : ∀ {Θ Ψ Γ A} {ι μ : Θ ⇒ᵐ Ψ} {t : Term Θ Γ A} → ι ≡ᵐ μ → [ ι ]ᵐ t ≈ [ μ ]ᵐ t
  []ᵐ-resp-≡ᵐ {t = tm-var x} ξ = ≈-≡ refl
  []ᵐ-resp-≡ᵐ {Θ} {Ψ} {Γ} {A} {ι = ι} {μ = μ} {t = tm-meta M ts} ξ =
    let open SetoidR (Term-setoid Ψ Γ A) in
    begin
    tm-meta (ι M) (λ i → [ ι ]ᵐ ts i) ≈⟨ ≈-meta (λ i → []ᵐ-resp-≡ᵐ ξ) ⟩
    tm-meta (ι M) (λ i → [ μ ]ᵐ ts i) ≈⟨ ≈-≡ ((cong λ N → tm-meta N (λ i → [ μ ]ᵐ ts i)) (ξ M)) ⟩
    tm-meta (μ M) (λ i → [ μ ]ᵐ ts i) ≈⟨ ≈-≡ refl ⟩
    tm-meta (μ M) (λ i → [ μ ]ᵐ ts i)
    ∎
  []ᵐ-resp-≡ᵐ {t = tm-oper f es} ξ = ≈-oper λ i → []ᵐ-resp-≡ᵐ ξ

  -- The action of the identity is trival
  [idᵐ] : ∀ {Θ Γ A} {t : Term Θ Γ A} → [ idᵐ ]ᵐ t ≈ t
  [idᵐ] {t = tm-var x} = ≈-refl
  [idᵐ] {t = tm-meta M ts} = ≈-meta λ i → [idᵐ]
  [idᵐ] {t = tm-oper f es} = ≈-oper λ i → [idᵐ]

  -- Extension respects composition
  ⇑ᵐ-resp-∘ᵐ : ∀ {Γ Δ Ξ Ψ} {ρ : Γ ⇒ᵐ Δ} {τ : Δ ⇒ᵐ Ξ} → ⇑ᵐ {Ω = Ψ} (τ ∘ᵐ ρ) ≡ᵐ (⇑ᵐ τ) ∘ᵐ (⇑ᵐ ρ)
  ⇑ᵐ-resp-∘ᵐ (var-inl x) = refl
  ⇑ᵐ-resp-∘ᵐ (var-inr y) = refl

  ᵐ⇑ᵐ-resp-∘ᵐ : ∀ {Θ Ψ Ω Ξ} {ρ : Θ ⇒ᵐ Ψ} {τ : Ψ ⇒ᵐ Ω}
    → ᵐ⇑ᵐ {Θ} {Ω} (τ ∘ᵐ ρ) {Ξ} ≡ᵐ (ᵐ⇑ᵐ τ) ∘ᵐ (ᵐ⇑ᵐ ρ)
  ᵐ⇑ᵐ-resp-∘ᵐ (var-inl M) = refl
  ᵐ⇑ᵐ-resp-∘ᵐ (var-inr N) = refl

  -- Extension of the identity renaming is the identity
  ⇑ᵐ-resp-idᵐ : ∀ {Θ Ψ} → (⇑ᵐ {Θ} {Θ} {Ψ}) (idᵐ {Θ}) ≡ᵐ idᵐ
  ⇑ᵐ-resp-idᵐ (var-inl M) = refl
  ⇑ᵐ-resp-idᵐ (var-inr N) = refl

  ᵐ⇑ᵐ-resp-idᵐ : ∀ {Θ Ψ} → (ᵐ⇑ᵐ {Θ} {Θ}) (idᵐ {Θ}) {Ψ} ≡ᵐ idᵐ
  ᵐ⇑ᵐ-resp-idᵐ (var-inl M) = refl
  ᵐ⇑ᵐ-resp-idᵐ (var-inr N) = refl

  -- Extension preserves equality of metavariable renamings
  ᵐ⇑ᵐ-resp-≡ᵐ : ∀ {Θ Ψ Ω} {ι μ : Θ ⇒ᵐ Ψ} → ι ≡ᵐ μ → ᵐ⇑ᵐ ι {Ω} ≡ᵐ ᵐ⇑ᵐ μ
  ᵐ⇑ᵐ-resp-≡ᵐ ι≡μ (var-inl M) = refl
  ᵐ⇑ᵐ-resp-≡ᵐ {ι = ι} ι≡μ (var-inr N) = cong (inrᵐ) (ι≡μ N)

  ⇑ᵐ-resp-≡ᵐ : ∀ {Θ Ψ Ω} {ι μ : Θ ⇒ᵐ Ψ} → ι ≡ᵐ μ → ⇑ᵐ {Ω = Ω} ι ≡ᵐ ⇑ᵐ μ
  ⇑ᵐ-resp-≡ᵐ ι≡μ (var-inl M) = cong var-inl (ι≡μ M)
  ⇑ᵐ-resp-≡ᵐ {ι = ι} ι≡μ (var-inr N) = refl


  -- The action of a renaming is functorial
  [∘ᵐ] : ∀ {Θ Ψ Ω Γ} {ι : Θ ⇒ᵐ Ψ} {μ : Ψ ⇒ᵐ Ω} {A} {t : Term Θ Γ A}
    → [ μ ∘ᵐ ι ]ᵐ t ≈ [ μ ]ᵐ ([ ι ]ᵐ t)
  [∘ᵐ] {t = tm-var x} = ≈-refl
  [∘ᵐ] {t = tm-meta M ts} = ≈-meta (λ i → [∘ᵐ])
  [∘ᵐ] {t = tm-oper f es} = ≈-oper (λ i → [∘ᵐ])

  ᵐ∘ᵛ≈ᵛ∘ᵐ : ∀ {Θ Ψ Γ Δ A} {ρ : Γ ⇒ᵛ Δ} {ι : Θ ⇒ᵐ Ψ} {t : Term Θ Γ A}
    → [ ι ]ᵐ ([ ρ ]ᵛ t) ≈ [ ρ ]ᵛ ([ ι ]ᵐ t)
  ᵐ∘ᵛ≈ᵛ∘ᵐ {t = tm-var x} = ≈-refl
  ᵐ∘ᵛ≈ᵛ∘ᵐ {t = tm-meta M ts} = ≈-meta (λ i → ᵐ∘ᵛ≈ᵛ∘ᵐ {t = ts i})
  ᵐ∘ᵛ≈ᵛ∘ᵐ {t = tm-oper f es} = ≈-oper (λ i → ᵐ∘ᵛ≈ᵛ∘ᵐ {t = es i})

  split-sum : ∀ {Θ Ψ Ξ Ω} {ι : Θ ⇒ᵐ Ψ} {μ : Ξ ⇒ᵐ Ω}
    → (μ +₁ ι) ≡ᵐ (⇑ᵐ μ) ∘ᵐ (ᵐ⇑ᵐ ι)
  split-sum (var-inl M) = refl
  split-sum (var-inr N) = refl

  split-sum2 : ∀ {Θ Ψ Ξ Ω} {ι : Θ ⇒ᵐ Ψ} {μ : Ξ ⇒ᵐ Ω}
    → (μ +₁ ι) ≡ᵐ (ᵐ⇑ᵐ ι) ∘ᵐ (⇑ᵐ μ)
  split-sum2 (var-inl M) = refl
  split-sum2 (var-inr N) = refl

  ⇑-resp-+ : ∀ {Θ Ψ Ξ Ω Γ A} {ι : Θ ⇒ᵐ Ψ} {μ : Ξ ⇒ᵐ Ω} {t : Term (Ξ + Θ) Γ A}
    → [ (⇑ᵐ μ) ]ᵐ ([ (ᵐ⇑ᵐ ι) ]ᵐ t) ≈ [ (ᵐ⇑ᵐ ι) ]ᵐ ([ (⇑ᵐ μ) ]ᵐ t)
  ⇑-resp-+ {Θ} {Ψ} {Ξ} {Ω} {Γ} {A} {ι} {μ} {t = t} =
    let open SetoidR (Term-setoid (Ω ,, Ψ) Γ A) in
    begin
    [ ⇑ᵐ μ ]ᵐ ([ ᵐ⇑ᵐ ι ]ᵐ t) ≈⟨ ≈-sym [∘ᵐ] ⟩
    [ (⇑ᵐ μ) ∘ᵐ (ᵐ⇑ᵐ ι) ]ᵐ t  ≈⟨ ≈-sym ([]ᵐ-resp-≡ᵐ split-sum) ⟩
    [ (μ +₁ ι) ]ᵐ t ≈⟨ []ᵐ-resp-≡ᵐ split-sum2 ⟩
    [(ᵐ⇑ᵐ ι) ∘ᵐ (⇑ᵐ μ)  ]ᵐ t ≈⟨ [∘ᵐ] ⟩
    [ ᵐ⇑ᵐ ι ]ᵐ ([ ⇑ᵐ μ ]ᵐ t)
    ∎

  ∘ᵐ-resp-⇑ : ∀ {Θ Ψ Ξ Ω} {ι : Θ ⇒ᵐ Ψ} {μ : Ψ ⇒ᵐ Ω}
    → ⇑ᵐ {Ω = Ξ}  (μ ∘ᵐ ι) ≡ᵐ ⇑ᵐ μ ∘ᵐ ⇑ᵐ ι
  ∘ᵐ-resp-⇑ (var-inl M) = refl
  ∘ᵐ-resp-⇑ (var-inr N) = refl

  ∘ᵐ-resp-⇑-term : ∀ {Θ Ψ Ξ Ω Γ A} {ι : Θ ⇒ᵐ Ψ} {μ : Ψ ⇒ᵐ Ω} {t : Term (Θ ,, Ξ) Γ A}
    → [ ⇑ᵐ {Ω = Ξ} (μ ∘ᵐ ι) ]ᵐ t ≈  [ ⇑ᵐ μ ]ᵐ ([ ⇑ᵐ ι ]ᵐ t)
  ∘ᵐ-resp-⇑-term {Θ} {Ψ} {Ξ} {Ω} {Γ} {A} {ι} {μ} {t = t} =
      let open SetoidR (Term-setoid (Ω ,, Ξ) Γ A) in
      begin
      [ ⇑ᵐ {Ω = Ξ} (μ ∘ᵐ ι) ]ᵐ t ≈⟨ []ᵐ-resp-≡ᵐ ∘ᵐ-resp-⇑ ⟩
      [ ⇑ᵐ μ ∘ᵐ ⇑ᵐ ι ]ᵐ t ≈⟨ [∘ᵐ] ⟩
      [ ⇑ᵐ μ ]ᵐ ([ ⇑ᵐ ι ]ᵐ t)
      ∎

  ∘ᵐ-resp-ᵐ⇑ : ∀ {Θ Ψ Ξ Ω} {ι : Θ ⇒ᵐ Ψ} {μ : Ψ ⇒ᵐ Ω}
    → ᵐ⇑ᵐ (μ ∘ᵐ ι) {Ω = Ξ} ≡ᵐ ᵐ⇑ᵐ μ ∘ᵐ ᵐ⇑ᵐ ι
  ∘ᵐ-resp-ᵐ⇑ (var-inl M) = refl
  ∘ᵐ-resp-ᵐ⇑ (var-inr N) = refl

  ∘ᵐ-resp-ᵐ⇑-term : ∀ {Θ Ψ Ξ Ω Γ A} {ι : Θ ⇒ᵐ Ψ} {μ : Ψ ⇒ᵐ Ω} {t : Term (Ξ ,, Θ) Γ A}
    → [ ᵐ⇑ᵐ  (μ ∘ᵐ ι) {Ω = Ξ} ]ᵐ t ≈  [ ᵐ⇑ᵐ μ ]ᵐ ([ ᵐ⇑ᵐ ι ]ᵐ t)
  ∘ᵐ-resp-ᵐ⇑-term {Θ} {Ψ} {Ξ} {Ω} {Γ} {A} {ι} {μ} {t = t} =
      let open SetoidR (Term-setoid (Ξ ,, Ω) Γ A) in
      begin
      [ ᵐ⇑ᵐ (μ ∘ᵐ ι) {Ω = Ξ} ]ᵐ t ≈⟨ []ᵐ-resp-≡ᵐ ∘ᵐ-resp-ᵐ⇑ ⟩
      [ ᵐ⇑ᵐ μ ∘ᵐ ᵐ⇑ᵐ ι ]ᵐ t ≈⟨ [∘ᵐ] ⟩
      [ ᵐ⇑ᵐ μ ]ᵐ ([ ᵐ⇑ᵐ ι ]ᵐ t)
      ∎


  vr-comm-mr : ∀ {Θ Ψ Γ Δ A} {ρ : Γ ⇒ᵛ Δ} {ι : Θ ⇒ᵐ Ψ} {t : Term Θ Γ A}
    → [ ι ]ᵐ ([ ρ ]ᵛ t) ≈ [ ρ ]ᵛ ([ ι ]ᵐ t)
  vr-comm-mr {t = tm-var x} = ≈-refl
  vr-comm-mr {t = tm-meta M ts} = ≈-meta (λ i → vr-comm-mr)
  vr-comm-mr {t = tm-oper f es} = ≈-oper (λ i → vr-comm-mr)

  mr-comm-vr : ∀ {Θ Ψ Γ Δ A} {ρ : Γ ⇒ᵛ Δ} {ι : Θ ⇒ᵐ Ψ} {t : Term Θ Γ A}
    → [ ρ ]ᵛ ([ ι ]ᵐ t) ≈  [ ι ]ᵐ ([ ρ ]ᵛ t)
  mr-comm-vr {t = tm-var x} = ≈-refl
  mr-comm-vr {t = tm-meta M ts} = ≈-meta (λ i → mr-comm-vr)
  mr-comm-vr {t = tm-oper f es} = ≈-oper (λ i → mr-comm-vr)

  module _ {Θ Ψ : MContext} {A : sort} where
    open Categories.Category
    open Categories.Category.Instance.Setoids
    open Categories.Functor
    open Categories.NaturalTransformation

    MRenaming-NT : ∀ (ι : Θ ⇒ᵐ Ψ) → NaturalTransformation (Term-Functor {Θ} {A}) (Term-Functor {Ψ} {A})
    MRenaming-NT ι =
      record
      { η = λ Γ → record { _⟨$⟩_ = [ ι ]ᵐ_ ; cong = []ᵐ-resp-≈ }
      ; commute = λ ρ t≈s → ≈-trans ([]ᵐ-resp-≈ ([]ᵛ-resp-≈ t≈s)) (ᵐ∘ᵛ≈ᵛ∘ᵐ)
      ; sym-commute = λ ρ t≈s → ≈-trans (≈-sym ᵐ∘ᵛ≈ᵛ∘ᵐ) ([]ᵐ-resp-≈ ([]ᵛ-resp-≈ t≈s))
      }
