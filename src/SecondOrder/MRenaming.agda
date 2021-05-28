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

--------------------------

  -- -- composition respects equality
  -- ∘ʳ-resp-≡ʳ : ∀ {Γ Δ Ξ} {τ₁ τ₂ : Δ ⇒ʳ Ξ} {σ₁ σ₂ : Γ ⇒ʳ Δ} →
  --                τ₁ ≡ʳ τ₂ → σ₁ ≡ʳ σ₂ → τ₁ ∘ʳ σ₁ ≡ʳ τ₂ ∘ʳ σ₂
  -- ∘ʳ-resp-≡ʳ {τ₁ = τ₁} {σ₂ = σ₂} ζ ξ x = trans (cong τ₁ (ξ x)) (ζ (σ₂ x))

  -- -- the identity is the unit

  -- identity-leftʳ : ∀ {Γ Δ} {ρ : Γ ⇒ʳ Δ} → idʳ ∘ʳ ρ ≡ʳ ρ
  -- identity-leftʳ ρ = refl

  -- identity-rightʳ : ∀ {Γ Δ} {ρ : Γ ⇒ʳ Δ} → ρ ∘ʳ idʳ ≡ʳ ρ
  -- identity-rightʳ ρ = refl

  -- -- composition is associative

  -- assocʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ʳ Δ} {ρ : Δ ⇒ʳ Ξ} {σ : Ξ ⇒ʳ Ψ} →
  --            (σ ∘ʳ ρ) ∘ʳ τ ≡ʳ σ ∘ʳ (ρ ∘ʳ τ)
  -- assocʳ x = refl

  -- sym-assocʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ʳ Δ} {ρ : Δ ⇒ʳ Ξ} {σ : Ξ ⇒ʳ Ψ} →
  --            σ ∘ʳ (ρ ∘ʳ τ) ≡ʳ (σ ∘ʳ ρ) ∘ʳ τ
  -- sym-assocʳ x = refl

  -- -- contexts and renamings form a category
  -- module _ where
  --   open Categories.Category

  --   Contexts : Category ℓ ℓ ℓ
  --   Contexts =
  --     record
  --       { Obj = VContext
  --       ; _⇒_ = _⇒ʳ_
  --       ; _≈_ = _≡ʳ_
  --       ; id = idʳ
  --       ; _∘_ = _∘ʳ_
  --       ; assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → assocʳ {τ = f} {ρ = g} {σ = h}
  --       ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → sym-assocʳ {τ = f} {ρ = g} {σ = h}
  --       ; identityˡ = λ x → refl
  --       ; identityʳ = λ x → refl
  --       ; identity² = λ x → refl
  --       ; equiv = record { refl = λ {ρ} {_} → ≡ʳ-refl {ρ = ρ} ; sym = ≡ʳ-sym ; trans = ≡ʳ-trans }
  --       ; ∘-resp-≈ = ∘ʳ-resp-≡ʳ
  --       }


  -- -- the coproduct structure of the category
  -- module _ where

  --   infixl 7 [_,_]ʳ

  --   [_,_]ʳ : ∀ {Γ Δ Ξ} → Γ ⇒ʳ Ξ → Δ ⇒ʳ Ξ → Γ ,, Δ ⇒ʳ Ξ
  --   [ σ , τ ]ʳ (var-inl x) = σ x
  --   [ σ , τ ]ʳ (var-inr y) = τ y

  --   inlʳ : ∀ {Γ Δ} → Γ ⇒ʳ Γ ,, Δ
  --   inlʳ = var-inl

  --   inrʳ : ∀ {Γ Δ} → Δ ⇒ʳ Γ ,, Δ
  --   inrʳ = var-inr

  --   uniqueʳ : ∀ {Γ Δ Ξ} {τ : Γ ,, Δ ⇒ʳ Ξ} {ρ : Γ ⇒ʳ Ξ} {σ : Δ ⇒ʳ Ξ}
  --             → τ ∘ʳ inlʳ ≡ʳ ρ
  --             → τ ∘ʳ inrʳ ≡ʳ σ
  --             → [ ρ , σ ]ʳ ≡ʳ τ
  --   uniqueʳ ξ ζ (var-inl x) = sym (ξ x)
  --   uniqueʳ ξ ζ (var-inr y) = sym (ζ y)

  --   Context-+ : Categories.Category.Cocartesian.BinaryCoproducts Contexts
  --   Context-+ =
  --     record {
  --       coproduct =
  --         λ {Γ Δ} →
  --         record
  --           { A+B = Γ ,, Δ
  --           ; i₁ = inlʳ
  --           ; i₂ = inrʳ
  --           ; [_,_] = [_,_]ʳ
  --           ; inject₁ = λ x → refl
  --           ; inject₂ = λ x → refl
  --           ; unique = uniqueʳ
  --           }
  --     }

  -- open Categories.Category.Cocartesian.BinaryCoproducts Context-+

  -- -- the renaming from the empty context

  -- inʳ : ∀ {Γ} → ctx-empty ⇒ʳ Γ
  -- inʳ ()

  -- -- extension of a renaming is summing with identity
  -- ⇑ʳ : ∀ {Γ Δ Ξ} → Γ ⇒ʳ Δ → Γ ,, Ξ ⇒ʳ Δ ,, Ξ
  -- ⇑ʳ ρ = ρ +₁ idʳ

  -- -- a renaming can also be extended on the right
  -- ʳ⇑ʳ : ∀ {Γ Δ} → Γ ⇒ʳ Δ → ∀ {Ξ} → Ξ ,, Γ ⇒ʳ Ξ ,, Δ
  -- ʳ⇑ʳ ρ = idʳ +₁ ρ


  -- -- the action of a renaming on terms
  -- module _ {Θ : MContext} where

  --   infix 6 [_]ʳ_

  --   [_]ʳ_ : ∀ {Γ Δ A} → Γ ⇒ʳ Δ → Term Θ Γ A → Term Θ Δ A
  --   [ ρ ]ʳ (tm-var x) = tm-var (ρ x)
  --   [ ρ ]ʳ (tm-meta M ts) = tm-meta M (λ i → [ ρ ]ʳ (ts i))
  --   [ ρ ]ʳ (tm-oper f es) = tm-oper f (λ i → [ ⇑ʳ ρ ]ʳ (es i))

  -- -- The sum of identities is an identity
  -- idʳ+idʳ : ∀ {Γ Δ} → idʳ {Γ = Γ} +₁ idʳ {Γ = Δ} ≡ʳ idʳ {Γ = Γ ,, Δ}
  -- idʳ+idʳ (var-inl x) = refl
  -- idʳ+idʳ (var-inr y) = refl

  -- -- The action of a renaming respects equality of terms
  -- []ʳ-resp-≈ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Γ ⇒ʳ Δ} → s ≈ t → [ ρ ]ʳ s ≈ [ ρ ]ʳ t
  -- []ʳ-resp-≈ (≈-≡ refl) = ≈-≡ refl
  -- []ʳ-resp-≈ (≈-meta ξ) = ≈-meta (λ i → []ʳ-resp-≈ (ξ i))
  -- []ʳ-resp-≈ (≈-oper ξ) = ≈-oper (λ i → []ʳ-resp-≈ (ξ i))

  -- -- The action of a renaming respects equality of renamings
  -- []ʳ-resp-≡ʳ : ∀ {Θ Γ Δ A} {ρ τ : Γ ⇒ʳ Δ} {t : Term Θ Γ A} → ρ ≡ʳ τ → [ ρ ]ʳ t ≈ [ τ ]ʳ t
  -- []ʳ-resp-≡ʳ {t = tm-var x} ξ = ≈-≡ (cong tm-var (ξ x))
  -- []ʳ-resp-≡ʳ {t = tm-meta M ts} ξ = ≈-meta (λ i → []ʳ-resp-≡ʳ ξ)
  -- []ʳ-resp-≡ʳ {t = tm-oper f es} ξ = ≈-oper (λ i → []ʳ-resp-≡ʳ (+₁-cong₂ ξ ≡ʳ-refl))

  -- -- The action of the identity is trival
  -- [id]ʳ : ∀ {Θ Γ A} {t : Term Θ Γ A} → [ idʳ ]ʳ t ≈ t
  -- [id]ʳ {t = tm-var x} = ≈-refl
  -- [id]ʳ {t = tm-meta M ts} = ≈-meta λ i → [id]ʳ
  -- [id]ʳ {t = tm-oper f es} = ≈-oper λ i → ≈-trans ([]ʳ-resp-≡ʳ idʳ+idʳ) [id]ʳ

  -- -- Extension respects composition
  -- ⇑ʳ-∘ʳ : ∀ {Γ Δ Ξ Ψ} {ρ : Γ ⇒ʳ Δ} {τ : Δ ⇒ʳ Ξ} → ⇑ʳ {Ξ = Ψ} (τ ∘ʳ ρ) ≡ʳ (⇑ʳ τ) ∘ʳ (⇑ʳ ρ)
  -- ⇑ʳ-∘ʳ (var-inl x) = refl
  -- ⇑ʳ-∘ʳ (var-inr y) = refl

  -- -- The action of a renaming is functorial
  -- [∘]ʳ : ∀ {Θ Γ Δ Ξ} {ρ : Γ ⇒ʳ Δ} {τ : Δ ⇒ʳ Ξ} {A} {t : Term Θ Γ A} → [ τ ∘ʳ ρ ]ʳ t ≈ [ τ ]ʳ ([ ρ ]ʳ t)
  -- [∘]ʳ {t = tm-var x} = ≈-refl
  -- [∘]ʳ {t = tm-meta M ts} = ≈-meta (λ i → [∘]ʳ)
  -- [∘]ʳ {t = tm-oper f es} = ≈-oper (λ i → ≈-trans ([]ʳ-resp-≡ʳ ⇑ʳ-∘ʳ) [∘]ʳ)

  -- -- Forming terms over a given metacontext and sort is functorial in the context
  -- module _ {Θ : MContext} {A : sort} where
  --   open Categories.Functor
  --   open Categories.Category.Instance.Setoids

  --   Term-Functor : Functor Contexts (Setoids ℓ ℓ)
  --   Term-Functor =
  --     record
  --       { F₀ = λ Γ → Term-setoid Θ Γ A
  --       ; F₁ = λ ρ → record { _⟨$⟩_ = [ ρ ]ʳ_ ; cong = []ʳ-resp-≈ }
  --       ; identity = ≈-trans [id]ʳ
  --       ; homomorphism = λ ξ → ≈-trans ([]ʳ-resp-≈ ξ) [∘]ʳ
  --       ; F-resp-≈ = λ ζ ξ → ≈-trans ([]ʳ-resp-≡ʳ ζ) ([]ʳ-resp-≈ ξ)
  --       }
