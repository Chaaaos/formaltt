open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)
import Function.Equality

import Categories.Category
import Categories.Functor
import Categories.Category.Instance.Setoids

import Categories.Category.Cocartesian

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Term

module SecondOrder.MRenaming
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ

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


  -- -- the coproduct structure of the category
  -- module _ where

  --   infixl 7 [_,_]ᵐʳ

  --   [_,_]ᵐʳ : ∀ {Γ Δ Ξ} → Γ ⇒ᵐʳ Ξ → Δ ⇒ᵐʳ Ξ → Γ ,, Δ ⇒ᵐʳ Ξ
  --   [ σ , τ ]ᵐʳ (var-inl x) = σ x
  --   [ σ , τ ]ᵐʳ (var-inr y) = τ y

  --   inlᵐʳ : ∀ {Γ Δ} → Γ ⇒ᵐʳ Γ ,, Δ
  --   inlᵐʳ = var-inl

  --   inrᵐʳ : ∀ {Γ Δ} → Δ ⇒ᵐʳ Γ ,, Δ
  --   inrᵐʳ = var-inr

  --   uniqueᵐʳ : ∀ {Γ Δ Ξ} {τ : Γ ,, Δ ⇒ᵐʳ Ξ} {ρ : Γ ⇒ᵐʳ Ξ} {σ : Δ ⇒ᵐʳ Ξ}
  --             → τ ∘ᵐʳ inlᵐʳ ≡ᵐʳ ρ
  --             → τ ∘ᵐʳ inrᵐʳ ≡ᵐʳ σ
  --             → [ ρ , σ ]ᵐʳ ≡ᵐʳ τ
  --   uniqueᵐʳ ξ ζ (var-inl x) = sym (ξ x)
  --   uniqueᵐʳ ξ ζ (var-inr y) = sym (ζ y)

  --   Context-+ : Categories.Category.Cocartesian.BinaryCoproducts Contexts
  --   Context-+ =
  --     record {
  --       coproduct =
  --         λ {Γ Δ} →
  --         record
  --           { A+B = Γ ,, Δ
  --           ; i₁ = inlᵐʳ
  --           ; i₂ = inrᵐʳ
  --           ; [_,_] = [_,_]ᵐʳ
  --           ; inject₁ = λ x → refl
  --           ; inject₂ = λ x → refl
  --           ; unique = uniqueᵐʳ
  --           }
  --     }

  -- open Categories.Category.Cocartesian.BinaryCoproducts Context-+

  -- -- the renaming from the empty context

  -- inᵐʳ : ∀ {Γ} → ctx-empty ⇒ᵐʳ Γ
  -- inᵐʳ ()

  -- -- extension of a renaming is summing with identity
  -- ⇑ᵐʳ : ∀ {Γ Δ Ξ} → Γ ⇒ᵐʳ Δ → Γ ,, Ξ ⇒ᵐʳ Δ ,, Ξ
  -- ⇑ᵐʳ ρ = ρ +₁ idᵐʳ

  -- -- a renaming can also be extended on the right
  -- ᵐʳ⇑ᵐʳ : ∀ {Γ Δ} → Γ ⇒ᵐʳ Δ → ∀ {Ξ} → Ξ ,, Γ ⇒ᵐʳ Ξ ,, Δ
  -- ᵐʳ⇑ᵐʳ ρ = idᵐʳ +₁ ρ


  -- -- the action of a renaming on terms
  -- module _ {Θ : MContext} where

  --   infix 6 [_]ᵐʳ_

  --   [_]ᵐʳ_ : ∀ {Γ Δ A} → Γ ⇒ᵐʳ Δ → Term Θ Γ A → Term Θ Δ A
  --   [ ρ ]ᵐʳ (tm-var x) = tm-var (ρ x)
  --   [ ρ ]ᵐʳ (tm-meta M ts) = tm-meta M (λ i → [ ρ ]ᵐʳ (ts i))
  --   [ ρ ]ᵐʳ (tm-oper f es) = tm-oper f (λ i → [ ⇑ᵐʳ ρ ]ᵐʳ (es i))

  -- -- The sum of identities is an identity
  -- idᵐʳ+idᵐʳ : ∀ {Γ Δ} → idᵐʳ {Γ = Γ} +₁ idᵐʳ {Γ = Δ} ≡ᵐʳ idᵐʳ {Γ = Γ ,, Δ}
  -- idᵐʳ+idᵐʳ (var-inl x) = refl
  -- idᵐʳ+idᵐʳ (var-inr y) = refl

  -- -- The action of a renaming respects equality of terms
  -- []ᵐʳ-resp-≈ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Γ ⇒ᵐʳ Δ} → s ≈ t → [ ρ ]ᵐʳ s ≈ [ ρ ]ᵐʳ t
  -- []ᵐʳ-resp-≈ (≈-≡ refl) = ≈-≡ refl
  -- []ᵐʳ-resp-≈ (≈-meta ξ) = ≈-meta (λ i → []ᵐʳ-resp-≈ (ξ i))
  -- []ᵐʳ-resp-≈ (≈-oper ξ) = ≈-oper (λ i → []ᵐʳ-resp-≈ (ξ i))

  -- -- The action of a renaming respects equality of renamings
  -- []ᵐʳ-resp-≡ᵐʳ : ∀ {Θ Γ Δ A} {ρ τ : Γ ⇒ᵐʳ Δ} {t : Term Θ Γ A} → ρ ≡ᵐʳ τ → [ ρ ]ᵐʳ t ≈ [ τ ]ᵐʳ t
  -- []ᵐʳ-resp-≡ᵐʳ {t = tm-var x} ξ = ≈-≡ (cong tm-var (ξ x))
  -- []ᵐʳ-resp-≡ᵐʳ {t = tm-meta M ts} ξ = ≈-meta (λ i → []ᵐʳ-resp-≡ᵐʳ ξ)
  -- []ᵐʳ-resp-≡ᵐʳ {t = tm-oper f es} ξ = ≈-oper (λ i → []ᵐʳ-resp-≡ᵐʳ (+₁-cong₂ ξ ≡ᵐʳ-refl))

  -- -- The action of the identity is trival
  -- [id]ᵐʳ : ∀ {Θ Γ A} {t : Term Θ Γ A} → [ idᵐʳ ]ᵐʳ t ≈ t
  -- [id]ᵐʳ {t = tm-var x} = ≈-refl
  -- [id]ᵐʳ {t = tm-meta M ts} = ≈-meta λ i → [id]ᵐʳ
  -- [id]ᵐʳ {t = tm-oper f es} = ≈-oper λ i → ≈-trans ([]ᵐʳ-resp-≡ᵐʳ idᵐʳ+idᵐʳ) [id]ᵐʳ

  -- -- Extension respects composition
  -- ⇑ᵐʳ-∘ᵐʳ : ∀ {Γ Δ Ξ Ψ} {ρ : Γ ⇒ᵐʳ Δ} {τ : Δ ⇒ᵐʳ Ξ} → ⇑ᵐʳ {Ξ = Ψ} (τ ∘ᵐʳ ρ) ≡ᵐʳ (⇑ᵐʳ τ) ∘ᵐʳ (⇑ᵐʳ ρ)
  -- ⇑ᵐʳ-∘ᵐʳ (var-inl x) = refl
  -- ⇑ᵐʳ-∘ᵐʳ (var-inr y) = refl

  -- -- The action of a renaming is functorial
  -- [∘]ᵐʳ : ∀ {Θ Γ Δ Ξ} {ρ : Γ ⇒ᵐʳ Δ} {τ : Δ ⇒ᵐʳ Ξ} {A} {t : Term Θ Γ A} → [ τ ∘ᵐʳ ρ ]ᵐʳ t ≈ [ τ ]ᵐʳ ([ ρ ]ᵐʳ t)
  -- [∘]ᵐʳ {t = tm-var x} = ≈-refl
  -- [∘]ᵐʳ {t = tm-meta M ts} = ≈-meta (λ i → [∘]ᵐʳ)
  -- [∘]ᵐʳ {t = tm-oper f es} = ≈-oper (λ i → ≈-trans ([]ᵐʳ-resp-≡ᵐʳ ⇑ᵐʳ-∘ᵐʳ) [∘]ᵐʳ)

  -- -- Forming terms over a given metacontext and sort is functorial in the context
  -- module _ {Θ : MContext} {A : sort} where
  --   open Categories.Functor
  --   open Categories.Category.Instance.Setoids

  --   Term-Functor : Functor Contexts (Setoids ℓ ℓ)
  --   Term-Functor =
  --     record
  --       { F₀ = λ Γ → Term-setoid Θ Γ A
  --       ; F₁ = λ ρ → record { _⟨$⟩_ = [ ρ ]ᵐʳ_ ; cong = []ᵐʳ-resp-≈ }
  --       ; identity = ≈-trans [id]ᵐʳ
  --       ; homomorphism = λ ξ → ≈-trans ([]ᵐʳ-resp-≈ ξ) [∘]ᵐʳ
  --       ; F-resp-≈ = λ ζ ξ → ≈-trans ([]ᵐʳ-resp-≡ᵐʳ ζ) ([]ᵐʳ-resp-≈ ξ)
  --       }
