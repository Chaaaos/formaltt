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
  _⇒ᵐʳ_ : ∀ (Θ ψ : MContext) → Set ℓ
  Θ ⇒ᵐʳ ψ = ∀ {Δ A} → [ Δ , A ]∈ Θ → [ Δ , A ]∈ ψ

  infix 4 _⇒ᵐʳ_

  -- equality of metarenamings

  _≡ᵐʳ_ : ∀ {Θ ψ} (ι μ : Θ ⇒ᵐʳ ψ) → Set ℓ
  _≡ᵐʳ_ {Θ} ι μ = ∀ {Δ A} (M : [ Δ , A ]∈ Θ) → ι M ≡ μ M

  infixl 3 _≡ᵐʳ_

  ≡ᵐʳ-refl : ∀ {Θ ψ} {ι : Θ ⇒ᵐʳ ψ} → ι ≡ᵐʳ ι
  ≡ᵐʳ-refl = λ M → refl

  ≡ᵐʳ-sym : ∀ {Θ ψ} {ι μ : Θ ⇒ᵐʳ ψ}
          → ι ≡ᵐʳ μ
          → μ ≡ᵐʳ ι
  ≡ᵐʳ-sym eq M = sym (eq M)

  ≡ᵐʳ-trans : ∀ {Θ ψ} {ι μ δ : Θ ⇒ᵐʳ ψ}
           → ι ≡ᵐʳ μ
           → μ ≡ᵐʳ δ
           → ι ≡ᵐʳ δ
  ≡ᵐʳ-trans eq1 eq2 M = trans (eq1 M) (eq2 M)

  -- meta-variable renamings form a setoid

  Mrenaming-setoid : ∀ (Θ ψ : MContext) → Setoid ℓ ℓ
  Mrenaming-setoid Θ ψ =
    record
      { Carrier = Θ ⇒ᵐʳ ψ
      ;  _≈_ = λ ι μ → ι ≡ᵐʳ μ
      ; isEquivalence =
                      record
                        { refl = λ {ι} M → ≡ᵐʳ-refl {Θ} {ψ} {ι} M
                        ; sym = ≡ᵐʳ-sym
                        ; trans = ≡ᵐʳ-trans
                        }
      }

  -- the identity renaming

  idᵐʳ : ∀ {Θ : MContext} → Θ ⇒ᵐʳ Θ
  idᵐʳ M = M

  -- equal metavariable renaming act the same on metavariables


  -- composition of renamings
  _∘ᵐʳ_ : ∀ {Θ ψ Ω} → ψ ⇒ᵐʳ Ω → Θ ⇒ᵐʳ ψ → Θ ⇒ᵐʳ Ω
  (ι ∘ᵐʳ μ) M = ι (μ M)

  infix 7 _∘ᵐʳ_

  -- composition respects equality
  ∘ᵐʳ-resp-≡ᵐʳ : ∀ {Γ Δ Ξ} {τ₁ τ₂ : Δ ⇒ᵐʳ Ξ} {σ₁ σ₂ : Γ ⇒ᵐʳ Δ} →
                 τ₁ ≡ᵐʳ τ₂ → σ₁ ≡ᵐʳ σ₂ → τ₁ ∘ᵐʳ σ₁ ≡ᵐʳ τ₂ ∘ᵐʳ σ₂
  ∘ᵐʳ-resp-≡ᵐʳ {τ₁ = τ₁} {σ₂ = σ₂} ζ ξ x = trans (cong τ₁ (ξ x)) (ζ (σ₂ x))

  -- the identity is the unit

  identity-leftᵐʳ : ∀ {Γ Δ} {ρ : Γ ⇒ᵐʳ Δ} → idᵐʳ ∘ᵐʳ ρ ≡ᵐʳ ρ
  identity-leftᵐʳ ρ = refl

  identity-rightᵐʳ : ∀ {Γ Δ} {ρ : Γ ⇒ᵐʳ Δ} → ρ ∘ᵐʳ idᵐʳ ≡ᵐʳ ρ
  identity-rightᵐʳ ρ = refl

  -- composition is associative

  assocᵐʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ᵐʳ Δ} {ρ : Δ ⇒ᵐʳ Ξ} {σ : Ξ ⇒ᵐʳ Ψ} →
             (σ ∘ᵐʳ ρ) ∘ᵐʳ τ ≡ᵐʳ σ ∘ᵐʳ (ρ ∘ᵐʳ τ)
  assocᵐʳ x = refl

  sym-assocᵐʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ᵐʳ Δ} {ρ : Δ ⇒ᵐʳ Ξ} {σ : Ξ ⇒ᵐʳ Ψ} →
             σ ∘ᵐʳ (ρ ∘ᵐʳ τ) ≡ᵐʳ (σ ∘ᵐʳ ρ) ∘ᵐʳ τ
  sym-assocᵐʳ x = refl

  -- contexts and renamings form a category
  module _ where
    open Categories.Category

    MContexts : Category ℓ ℓ ℓ
    MContexts =
      record
        { Obj = MContext
        ; _⇒_ = _⇒ᵐʳ_
        ; _≈_ = _≡ᵐʳ_
        ; id = idᵐʳ
        ; _∘_ = _∘ᵐʳ_
        ; assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → assocᵐʳ {τ = f} {ρ = g} {σ = h}
        ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → sym-assocᵐʳ {τ = f} {ρ = g} {σ = h}
        ; identityˡ = λ x → refl
        ; identityʳ = λ x → refl
        ; identity² = λ x → refl
        ; equiv = record { refl = λ {ι} {_} → ≡ᵐʳ-refl {ι = ι} ; sym = ≡ᵐʳ-sym ; trans = ≡ᵐʳ-trans }
        ; ∘-resp-≈ = ∘ᵐʳ-resp-≡ᵐʳ
        }


  -- the coproduct structure of the category
  module _ where

    infixl 7 [_,_]ᵐʳ

    [_,_]ᵐʳ : ∀ {Γ Δ Ξ} → Γ ⇒ᵐʳ Ξ → Δ ⇒ᵐʳ Ξ → Γ ,, Δ ⇒ᵐʳ Ξ
    [ σ , τ ]ᵐʳ (var-inl x) = σ x
    [ σ , τ ]ᵐʳ (var-inr y) = τ y

    inlᵐʳ : ∀ {Γ Δ} → Γ ⇒ᵐʳ Γ ,, Δ
    inlᵐʳ = var-inl

    inrᵐʳ : ∀ {Γ Δ} → Δ ⇒ᵐʳ Γ ,, Δ
    inrᵐʳ = var-inr

    uniqueᵐʳ : ∀ {Γ Δ Ξ} {τ : Γ ,, Δ ⇒ᵐʳ Ξ} {ρ : Γ ⇒ᵐʳ Ξ} {σ : Δ ⇒ᵐʳ Ξ}
              → τ ∘ᵐʳ inlᵐʳ ≡ᵐʳ ρ
              → τ ∘ᵐʳ inrᵐʳ ≡ᵐʳ σ
              → [ ρ , σ ]ᵐʳ ≡ᵐʳ τ
    uniqueᵐʳ ξ ζ (var-inl x) = sym (ξ x)
    uniqueᵐʳ ξ ζ (var-inr y) = sym (ζ y)

    MContext-+ : Categories.Category.Cocartesian.BinaryCoproducts MContexts
    MContext-+ =
      record {
        coproduct =
          λ {Γ Δ} →
          record
            { A+B = Γ ,, Δ
            ; i₁ = inlᵐʳ
            ; i₂ = inrᵐʳ
            ; [_,_] = [_,_]ᵐʳ
            ; inject₁ = λ x → refl
            ; inject₂ = λ x → refl
            ; unique = uniqueᵐʳ
            }
      }

  open Categories.Category.Cocartesian.BinaryCoproducts MContext-+

  -- the renaming from the empty context

  inᵐʳ : ∀ {Γ} → ctx-empty ⇒ᵐʳ Γ
  inᵐʳ ()

  -- extension of a renaming is summing with identity
  ⇑ᵐʳ : ∀ {Θ Ψ Ω} → Θ ⇒ᵐʳ Ψ → Θ ,, Ω ⇒ᵐʳ Ψ ,, Ω
  ⇑ᵐʳ ρ = ρ +₁ idᵐʳ

  -- a renaming can also be extended on the right
  ᵐʳ⇑ᵐʳ : ∀ {Θ Ψ} → Θ ⇒ᵐʳ Ψ → ∀ {Ω} → Ω ,, Θ ⇒ᵐʳ Ω ,, Ψ
  ᵐʳ⇑ᵐʳ ρ = idᵐʳ +₁ ρ


  -- the action of a metavariable renaming on terms
  infix 6 [_]ᵐʳ_

  [_]ᵐʳ_ : ∀ {Θ Ψ Γ A} → Θ ⇒ᵐʳ Ψ → Term Θ Γ A → Term Ψ Γ A
  [ ι ]ᵐʳ (tm-var x) = tm-var x
  [ ι ]ᵐʳ (tm-meta M ts) = tm-meta (ι M) (λ i → [ ι ]ᵐʳ ts i)
  [ ι ]ᵐʳ (tm-oper f es) = tm-oper f (λ i → [ ι ]ᵐʳ es i)

  -- The sum of identities is an identity
  idᵐʳ+idᵐʳ : ∀ {Θ Ψ} → idᵐʳ {Θ = Θ} +₁ idᵐʳ {Θ = Ψ} ≡ᵐʳ idᵐʳ {Θ = Θ ,, Ψ}
  idᵐʳ+idᵐʳ (var-inl x) = refl
  idᵐʳ+idᵐʳ (var-inr y) = refl

  -- The action of a renaming respects equality of terms
  []ᵐʳ-resp-≈ : ∀ {Θ Ψ Γ A} {s t : Term Θ Γ A} {ι : Θ ⇒ᵐʳ Ψ} → s ≈ t → [ ι ]ᵐʳ s ≈ [ ι ]ᵐʳ t
  []ᵐʳ-resp-≈ (≈-≡ refl) = ≈-≡ refl
  []ᵐʳ-resp-≈ (≈-meta ξ) = ≈-meta (λ i → []ᵐʳ-resp-≈ (ξ i))
  []ᵐʳ-resp-≈ (≈-oper ξ) = ≈-oper (λ i → []ᵐʳ-resp-≈ (ξ i))

  -- The action of a renaming respects equality of renamings
  []ᵐʳ-resp-≡ᵐʳ : ∀ {Θ Ψ Γ A} {ι μ : Θ ⇒ᵐʳ Ψ} {t : Term Θ Γ A} → ι ≡ᵐʳ μ → [ ι ]ᵐʳ t ≈ [ μ ]ᵐʳ t
  []ᵐʳ-resp-≡ᵐʳ {t = tm-var x} ξ = ≈-≡ refl
  []ᵐʳ-resp-≡ᵐʳ {Θ} {Ψ} {Γ} {A} {ι = ι} {μ = μ} {t = tm-meta M ts} ξ =
    let open SetoidR (Term-setoid Ψ Γ A) in
    begin
    tm-meta (ι M) (λ i → [ ι ]ᵐʳ ts i) ≈⟨ ≈-meta (λ i → []ᵐʳ-resp-≡ᵐʳ ξ) ⟩
    tm-meta (ι M) (λ i → [ μ ]ᵐʳ ts i) ≈⟨ ≈-≡ ((cong λ N → tm-meta N (λ i → [ μ ]ᵐʳ ts i)) (ξ M)) ⟩
    tm-meta (μ M) (λ i → [ μ ]ᵐʳ ts i) ≈⟨ ≈-≡ refl ⟩
    tm-meta (μ M) (λ i → [ μ ]ᵐʳ ts i)
    ∎
  []ᵐʳ-resp-≡ᵐʳ {t = tm-oper f es} ξ = ≈-oper λ i → []ᵐʳ-resp-≡ᵐʳ ξ

  -- The action of the identity is trival
  [id]ᵐʳ : ∀ {Θ Γ A} {t : Term Θ Γ A} → [ idᵐʳ ]ᵐʳ t ≈ t
  [id]ᵐʳ {t = tm-var x} = ≈-refl
  [id]ᵐʳ {t = tm-meta M ts} = ≈-meta λ i → [id]ᵐʳ
  [id]ᵐʳ {t = tm-oper f es} = ≈-oper λ i → [id]ᵐʳ

  -- Extension respects composition
  ⇑ᵐʳ-∘ᵐʳ : ∀ {Γ Δ Ξ Ψ} {ρ : Γ ⇒ᵐʳ Δ} {τ : Δ ⇒ᵐʳ Ξ} → ⇑ᵐʳ {Ω = Ψ} (τ ∘ᵐʳ ρ) ≡ᵐʳ (⇑ᵐʳ τ) ∘ᵐʳ (⇑ᵐʳ ρ)
  ⇑ᵐʳ-∘ᵐʳ (var-inl x) = refl
  ⇑ᵐʳ-∘ᵐʳ (var-inr y) = refl

  ᵐʳ⇑ᵐʳ-∘ᵐʳ : ∀ {Θ Ψ Ω Ξ} {ρ : Θ ⇒ᵐʳ Ψ} {τ : Ψ ⇒ᵐʳ Ω}
    → ᵐʳ⇑ᵐʳ {Θ} {Ω} (τ ∘ᵐʳ ρ) {Ξ} ≡ᵐʳ (ᵐʳ⇑ᵐʳ τ) ∘ᵐʳ (ᵐʳ⇑ᵐʳ ρ)
  ᵐʳ⇑ᵐʳ-∘ᵐʳ (var-inl M) = refl
  ᵐʳ⇑ᵐʳ-∘ᵐʳ (var-inr N) = refl

  -- Extension of the identity renaming is the identity
  ⇑ᵐʳid≡ᵐʳidᵐʳ : ∀ {Θ Ψ} → (⇑ᵐʳ {Θ} {Θ} {Ψ}) (idᵐʳ {Θ}) ≡ᵐʳ idᵐʳ
  ⇑ᵐʳid≡ᵐʳidᵐʳ (var-inl M) = refl
  ⇑ᵐʳid≡ᵐʳidᵐʳ (var-inr N) = refl

  ᵐʳ⇑ᵐʳid≡ᵐʳidᵐʳ : ∀ {Θ Ψ} → (ᵐʳ⇑ᵐʳ {Θ} {Θ}) (idᵐʳ {Θ}) {Ψ} ≡ᵐʳ idᵐʳ
  ᵐʳ⇑ᵐʳid≡ᵐʳidᵐʳ (var-inl M) = refl
  ᵐʳ⇑ᵐʳid≡ᵐʳidᵐʳ (var-inr N) = refl

  -- Extension preserves equality of metavariable renamings
  ᵐʳ⇑ᵐʳ-resp-≡ᵐʳ : ∀ {Θ Ψ Ω} {ι μ : Θ ⇒ᵐʳ Ψ} → ι ≡ᵐʳ μ → ᵐʳ⇑ᵐʳ ι {Ω} ≡ᵐʳ ᵐʳ⇑ᵐʳ μ
  ᵐʳ⇑ᵐʳ-resp-≡ᵐʳ ι≡μ (var-inl M) = refl
  ᵐʳ⇑ᵐʳ-resp-≡ᵐʳ {ι = ι} ι≡μ (var-inr N) = cong (inrᵐʳ) (ι≡μ N)

  ⇑ᵐʳ-resp-≡ᵐʳ : ∀ {Θ Ψ Ω} {ι μ : Θ ⇒ᵐʳ Ψ} → ι ≡ᵐʳ μ → ⇑ᵐʳ {Ω = Ω} ι ≡ᵐʳ ⇑ᵐʳ μ
  ⇑ᵐʳ-resp-≡ᵐʳ ι≡μ (var-inl M) = cong var-inl (ι≡μ M)
  ⇑ᵐʳ-resp-≡ᵐʳ {ι = ι} ι≡μ (var-inr N) = refl


  -- The action of a renaming is functorial
  [∘]ᵐʳ : ∀ {Θ Ψ Ω Γ} {ι : Θ ⇒ᵐʳ Ψ} {μ : Ψ ⇒ᵐʳ Ω} {A} {t : Term Θ Γ A}
    → [ μ ∘ᵐʳ ι ]ᵐʳ t ≈ [ μ ]ᵐʳ ([ ι ]ᵐʳ t)
  [∘]ᵐʳ {t = tm-var x} = ≈-refl
  [∘]ᵐʳ {t = tm-meta M ts} = ≈-meta (λ i → [∘]ᵐʳ)
  [∘]ᵐʳ {t = tm-oper f es} = ≈-oper (λ i → [∘]ᵐʳ)

  ᵐʳ∘ᵛʳ≈ᵛʳ∘ᵐʳ : ∀ {Θ Ψ Γ Δ A} {ρ : Γ ⇒ᵛʳ Δ} {ι : Θ ⇒ᵐʳ Ψ} {t : Term Θ Γ A}
    → [ ι ]ᵐʳ ([ ρ ]ᵛʳ t) ≈ [ ρ ]ᵛʳ ([ ι ]ᵐʳ t)
  ᵐʳ∘ᵛʳ≈ᵛʳ∘ᵐʳ {t = tm-var x} = ≈-refl
  ᵐʳ∘ᵛʳ≈ᵛʳ∘ᵐʳ {t = tm-meta M ts} = ≈-meta (λ i → ᵐʳ∘ᵛʳ≈ᵛʳ∘ᵐʳ {t = ts i})
  ᵐʳ∘ᵛʳ≈ᵛʳ∘ᵐʳ {t = tm-oper f es} = ≈-oper (λ i → ᵐʳ∘ᵛʳ≈ᵛʳ∘ᵐʳ {t = es i})

  split-sum : ∀ {Θ Ψ Ξ Ω} {ι : Θ ⇒ᵐʳ Ψ} {μ : Ξ ⇒ᵐʳ Ω}
    → (μ +₁ ι) ≡ᵐʳ (⇑ᵐʳ μ) ∘ᵐʳ (ᵐʳ⇑ᵐʳ ι)
  split-sum (var-inl M) = refl
  split-sum (var-inr N) = refl

  split-sum2 : ∀ {Θ Ψ Ξ Ω} {ι : Θ ⇒ᵐʳ Ψ} {μ : Ξ ⇒ᵐʳ Ω}
    → (μ +₁ ι) ≡ᵐʳ (ᵐʳ⇑ᵐʳ ι) ∘ᵐʳ (⇑ᵐʳ μ)
  split-sum2 (var-inl M) = refl
  split-sum2 (var-inr N) = refl

  ⇑-resp-+ : ∀ {Θ Ψ Ξ Ω Γ A} {ι : Θ ⇒ᵐʳ Ψ} {μ : Ξ ⇒ᵐʳ Ω} {t : Term (Ξ + Θ) Γ A}
    → [ (⇑ᵐʳ μ) ]ᵐʳ ([ (ᵐʳ⇑ᵐʳ ι) ]ᵐʳ t) ≈ [ (ᵐʳ⇑ᵐʳ ι) ]ᵐʳ ([ (⇑ᵐʳ μ) ]ᵐʳ t)
  ⇑-resp-+ {Θ} {Ψ} {Ξ} {Ω} {Γ} {A} {ι} {μ} {t = t} =
    let open SetoidR (Term-setoid (Ω ,, Ψ) Γ A) in
    begin
    [ ⇑ᵐʳ μ ]ᵐʳ ([ ᵐʳ⇑ᵐʳ ι ]ᵐʳ t) ≈⟨ ≈-sym [∘]ᵐʳ ⟩
    [ (⇑ᵐʳ μ) ∘ᵐʳ (ᵐʳ⇑ᵐʳ ι) ]ᵐʳ t  ≈⟨ ≈-sym ([]ᵐʳ-resp-≡ᵐʳ split-sum) ⟩
    [ (μ +₁ ι) ]ᵐʳ t ≈⟨ []ᵐʳ-resp-≡ᵐʳ split-sum2 ⟩
    [(ᵐʳ⇑ᵐʳ ι) ∘ᵐʳ (⇑ᵐʳ μ)  ]ᵐʳ t ≈⟨ [∘]ᵐʳ ⟩
    [ ᵐʳ⇑ᵐʳ ι ]ᵐʳ ([ ⇑ᵐʳ μ ]ᵐʳ t)
    ∎

  ∘ᵐʳ-resp-⇑ : ∀ {Θ Ψ Ξ Ω} {ι : Θ ⇒ᵐʳ Ψ} {μ : Ψ ⇒ᵐʳ Ω} 
    → ⇑ᵐʳ {Ω = Ξ}  (μ ∘ᵐʳ ι) ≡ᵐʳ ⇑ᵐʳ μ ∘ᵐʳ ⇑ᵐʳ ι
  ∘ᵐʳ-resp-⇑ (var-inl M) = refl
  ∘ᵐʳ-resp-⇑ (var-inr N) = refl

  ∘ᵐʳ-resp-⇑-term : ∀ {Θ Ψ Ξ Ω Γ A} {ι : Θ ⇒ᵐʳ Ψ} {μ : Ψ ⇒ᵐʳ Ω} {t : Term (Θ ,, Ξ) Γ A}
    → [ ⇑ᵐʳ {Ω = Ξ} (μ ∘ᵐʳ ι) ]ᵐʳ t ≈  [ ⇑ᵐʳ μ ]ᵐʳ ([ ⇑ᵐʳ ι ]ᵐʳ t)
  ∘ᵐʳ-resp-⇑-term {Θ} {Ψ} {Ξ} {Ω} {Γ} {A} {ι} {μ} {t = t} =
      let open SetoidR (Term-setoid (Ω ,, Ξ) Γ A) in
      begin
      [ ⇑ᵐʳ {Ω = Ξ} (μ ∘ᵐʳ ι) ]ᵐʳ t ≈⟨ []ᵐʳ-resp-≡ᵐʳ ∘ᵐʳ-resp-⇑ ⟩
      [ ⇑ᵐʳ μ ∘ᵐʳ ⇑ᵐʳ ι ]ᵐʳ t ≈⟨ [∘]ᵐʳ ⟩
      [ ⇑ᵐʳ μ ]ᵐʳ ([ ⇑ᵐʳ ι ]ᵐʳ t)
      ∎

  ∘ᵐʳ-resp-ᵐʳ⇑ : ∀ {Θ Ψ Ξ Ω} {ι : Θ ⇒ᵐʳ Ψ} {μ : Ψ ⇒ᵐʳ Ω} 
    → ᵐʳ⇑ᵐʳ (μ ∘ᵐʳ ι) {Ω = Ξ} ≡ᵐʳ ᵐʳ⇑ᵐʳ μ ∘ᵐʳ ᵐʳ⇑ᵐʳ ι
  ∘ᵐʳ-resp-ᵐʳ⇑ (var-inl M) = refl
  ∘ᵐʳ-resp-ᵐʳ⇑ (var-inr N) = refl

  ∘ᵐʳ-resp-ᵐʳ⇑-term : ∀ {Θ Ψ Ξ Ω Γ A} {ι : Θ ⇒ᵐʳ Ψ} {μ : Ψ ⇒ᵐʳ Ω} {t : Term (Ξ ,, Θ) Γ A}
    → [ ᵐʳ⇑ᵐʳ  (μ ∘ᵐʳ ι) {Ω = Ξ} ]ᵐʳ t ≈  [ ᵐʳ⇑ᵐʳ μ ]ᵐʳ ([ ᵐʳ⇑ᵐʳ ι ]ᵐʳ t)
  ∘ᵐʳ-resp-ᵐʳ⇑-term {Θ} {Ψ} {Ξ} {Ω} {Γ} {A} {ι} {μ} {t = t} =
      let open SetoidR (Term-setoid (Ξ ,, Ω) Γ A) in
      begin
      [ ᵐʳ⇑ᵐʳ (μ ∘ᵐʳ ι) {Ω = Ξ} ]ᵐʳ t ≈⟨ []ᵐʳ-resp-≡ᵐʳ ∘ᵐʳ-resp-ᵐʳ⇑ ⟩
      [ ᵐʳ⇑ᵐʳ μ ∘ᵐʳ ᵐʳ⇑ᵐʳ ι ]ᵐʳ t ≈⟨ [∘]ᵐʳ ⟩
      [ ᵐʳ⇑ᵐʳ μ ]ᵐʳ ([ ᵐʳ⇑ᵐʳ ι ]ᵐʳ t)
      ∎


  vr-comm-mr : ∀ {Θ Ψ Γ Δ A} {ρ : Γ ⇒ᵛʳ Δ} {ι : Θ ⇒ᵐʳ Ψ} {t : Term Θ Γ A}
    → [ ι ]ᵐʳ ([ ρ ]ᵛʳ t) ≈ [ ρ ]ᵛʳ ([ ι ]ᵐʳ t)
  vr-comm-mr {t = tm-var x} = ≈-refl
  vr-comm-mr {t = tm-meta M ts} = ≈-meta (λ i → vr-comm-mr)
  vr-comm-mr {t = tm-oper f es} = ≈-oper (λ i → vr-comm-mr)

  mr-comm-vr : ∀ {Θ Ψ Γ Δ A} {ρ : Γ ⇒ᵛʳ Δ} {ι : Θ ⇒ᵐʳ Ψ} {t : Term Θ Γ A}
    → [ ρ ]ᵛʳ ([ ι ]ᵐʳ t) ≈  [ ι ]ᵐʳ ([ ρ ]ᵛʳ t)
  mr-comm-vr {t = tm-var x} = ≈-refl
  mr-comm-vr {t = tm-meta M ts} = ≈-meta (λ i → mr-comm-vr)
  mr-comm-vr {t = tm-oper f es} = ≈-oper (λ i → mr-comm-vr)

  module _ {Θ Ψ : MContext} {A : sort} where
    open Categories.Category
    open Categories.Category.Instance.Setoids
    open Categories.Functor
    open Categories.NaturalTransformation

    MRenaming-NT : ∀ (ι : Θ ⇒ᵐʳ Ψ) → NaturalTransformation (Term-Functor {Θ} {A}) (Term-Functor {Ψ} {A})
    MRenaming-NT ι =
      record
      { η = λ Γ → record { _⟨$⟩_ = [ ι ]ᵐʳ_ ; cong = []ᵐʳ-resp-≈ }
      ; commute = λ ρ t≈s → ≈-trans ([]ᵐʳ-resp-≈ ([]ᵛʳ-resp-≈ t≈s)) (ᵐʳ∘ᵛʳ≈ᵛʳ∘ᵐʳ)
      ; sym-commute = λ ρ t≈s → ≈-trans (≈-sym ᵐʳ∘ᵛʳ≈ᵛʳ∘ᵐʳ) ([]ᵐʳ-resp-≈ ([]ᵛʳ-resp-≈ t≈s))
      }

