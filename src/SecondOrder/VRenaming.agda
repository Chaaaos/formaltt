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

module SecondOrder.VRenaming
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ

  -- a renaming maps variables between contexts in a type-preserving way
  _⇒ᵛʳ_ : ∀ (Γ Δ : VContext) → Set ℓ
  Γ ⇒ᵛʳ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

  infix 4 _⇒ᵛʳ_

  -- equality of renamings

  _≡ᵛʳ_ : ∀ {Γ Δ} (σ τ : Γ ⇒ᵛʳ Δ) → Set ℓ
  _≡ᵛʳ_ {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≡ τ x

  infixl 3 _≡ᵛʳ_

  ≡ᵛʳ-refl : ∀ {Γ Δ} {ρ : Γ ⇒ᵛʳ Δ} → ρ ≡ᵛʳ ρ
  ≡ᵛʳ-refl = λ x → refl

  ≡ᵛʳ-sym : ∀ {Γ Δ} {ρ ν : Γ ⇒ᵛʳ Δ}
          → ρ ≡ᵛʳ ν
          → ν ≡ᵛʳ ρ
  ≡ᵛʳ-sym eq x = sym (eq x)

  ≡ᵛʳ-trans : ∀ {Γ Δ} {ρ ν γ : Γ ⇒ᵛʳ Δ}
           → ρ ≡ᵛʳ ν
           → ν ≡ᵛʳ γ
           → ρ ≡ᵛʳ γ
  ≡ᵛʳ-trans eq1 eq2 x = trans (eq1 x) (eq2 x)

  -- renamings form a setoid

  renaming-setoid : ∀ (Γ Δ : VContext) → Setoid ℓ ℓ
  renaming-setoid Γ Δ =
    record
      { Carrier = Γ ⇒ᵛʳ Δ
      ;  _≈_ = λ ρ ν → ρ ≡ᵛʳ ν
      ; isEquivalence =
                      record
                        { refl = λ {ρ} x → ≡ᵛʳ-refl {Γ} {Δ} {ρ} x
                        ; sym = ≡ᵛʳ-sym
                        ; trans = ≡ᵛʳ-trans
                        }
      }

  -- renaming preserves equality of variables
  ρ-resp-≡ : ∀ {Γ Δ A} {x y : A ∈ Γ} {ρ : Γ ⇒ᵛʳ Δ} → x ≡ y → ρ x ≡ ρ y
  ρ-resp-≡ refl = refl

  -- the identity renaming

  idᵛʳ : ∀ {Γ : VContext} → Γ ⇒ᵛʳ Γ
  idᵛʳ x = x

  -- composition of renamings
  _∘ᵛʳ_ : ∀ {Γ Δ Ξ} → Δ ⇒ᵛʳ Ξ → Γ ⇒ᵛʳ Δ → Γ ⇒ᵛʳ Ξ
  (σ ∘ᵛʳ ρ) x = σ (ρ x)

  infix 7 _∘ᵛʳ_

  -- composition respects equality
  ∘ᵛʳ-resp-≡ᵛʳ : ∀ {Γ Δ Ξ} {τ₁ τ₂ : Δ ⇒ᵛʳ Ξ} {σ₁ σ₂ : Γ ⇒ᵛʳ Δ} →
                 τ₁ ≡ᵛʳ τ₂ → σ₁ ≡ᵛʳ σ₂ → τ₁ ∘ᵛʳ σ₁ ≡ᵛʳ τ₂ ∘ᵛʳ σ₂
  ∘ᵛʳ-resp-≡ᵛʳ {τ₁ = τ₁} {σ₂ = σ₂} ζ ξ x = trans (cong τ₁ (ξ x)) (ζ (σ₂ x))

  -- the identity is the unit

  identity-leftᵛʳ : ∀ {Γ Δ} {ρ : Γ ⇒ᵛʳ Δ} → idᵛʳ ∘ᵛʳ ρ ≡ᵛʳ ρ
  identity-leftᵛʳ ρ = refl

  identity-rightᵛʳ : ∀ {Γ Δ} {ρ : Γ ⇒ᵛʳ Δ} → ρ ∘ᵛʳ idᵛʳ ≡ᵛʳ ρ
  identity-rightᵛʳ ρ = refl

  -- composition is associative

  assocᵛʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ᵛʳ Δ} {ρ : Δ ⇒ᵛʳ Ξ} {σ : Ξ ⇒ᵛʳ Ψ} →
             (σ ∘ᵛʳ ρ) ∘ᵛʳ τ ≡ᵛʳ σ ∘ᵛʳ (ρ ∘ᵛʳ τ)
  assocᵛʳ x = refl

  sym-assocᵛʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ᵛʳ Δ} {ρ : Δ ⇒ᵛʳ Ξ} {σ : Ξ ⇒ᵛʳ Ψ} →
             σ ∘ᵛʳ (ρ ∘ᵛʳ τ) ≡ᵛʳ (σ ∘ᵛʳ ρ) ∘ᵛʳ τ
  sym-assocᵛʳ x = refl

  -- contexts and renamings form a category
  module _ where
    open Categories.Category

    VContexts : Category ℓ ℓ ℓ
    VContexts =
      record
        { Obj = VContext
        ; _⇒_ = _⇒ᵛʳ_
        ; _≈_ = _≡ᵛʳ_
        ; id = idᵛʳ
        ; _∘_ = _∘ᵛʳ_
        ; assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → assocᵛʳ {τ = f} {ρ = g} {σ = h}
        ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → sym-assocᵛʳ {τ = f} {ρ = g} {σ = h}
        ; identityˡ = λ x → refl
        ; identityʳ = λ x → refl
        ; identity² = λ x → refl
        ; equiv = record { refl = λ {ρ} {_} → ≡ᵛʳ-refl {ρ = ρ} ; sym = ≡ᵛʳ-sym ; trans = ≡ᵛʳ-trans }
        ; ∘-resp-≈ = ∘ᵛʳ-resp-≡ᵛʳ
        }


  -- the coproduct structure of the category
  module _ where

    infixl 7 [_,_]ᵛʳ

    [_,_]ᵛʳ : ∀ {Γ Δ Ξ} → Γ ⇒ᵛʳ Ξ → Δ ⇒ᵛʳ Ξ → Γ ,, Δ ⇒ᵛʳ Ξ
    [ σ , τ ]ᵛʳ (var-inl x) = σ x
    [ σ , τ ]ᵛʳ (var-inr y) = τ y

    inlᵛʳ : ∀ {Γ Δ} → Γ ⇒ᵛʳ Γ ,, Δ
    inlᵛʳ = var-inl

    inrᵛʳ : ∀ {Γ Δ} → Δ ⇒ᵛʳ Γ ,, Δ
    inrᵛʳ = var-inr

    uniqueᵛʳ : ∀ {Γ Δ Ξ} {τ : Γ ,, Δ ⇒ᵛʳ Ξ} {ρ : Γ ⇒ᵛʳ Ξ} {σ : Δ ⇒ᵛʳ Ξ}
              → τ ∘ᵛʳ inlᵛʳ ≡ᵛʳ ρ
              → τ ∘ᵛʳ inrᵛʳ ≡ᵛʳ σ
              → [ ρ , σ ]ᵛʳ ≡ᵛʳ τ
    uniqueᵛʳ ξ ζ (var-inl x) = sym (ξ x)
    uniqueᵛʳ ξ ζ (var-inr y) = sym (ζ y)

    Context-+ : Categories.Category.Cocartesian.BinaryCoproducts VContexts
    Context-+ =
      record {
        coproduct =
          λ {Γ Δ} →
          record
            { A+B = Γ ,, Δ
            ; i₁ = inlᵛʳ
            ; i₂ = inrᵛʳ
            ; [_,_] = [_,_]ᵛʳ
            ; inject₁ = λ x → refl
            ; inject₂ = λ x → refl
            ; unique = uniqueᵛʳ
            }
      }

  open Categories.Category.Cocartesian.BinaryCoproducts Context-+

  -- the renaming from the empty context

  inᵛʳ : ∀ {Γ} → ctx-empty ⇒ᵛʳ Γ
  inᵛʳ ()

  -- extension of a renaming is summing with identity
  ⇑ᵛʳ : ∀ {Γ Δ Ξ} → Γ ⇒ᵛʳ Δ → Γ ,, Ξ ⇒ᵛʳ Δ ,, Ξ
  ⇑ᵛʳ ρ = ρ +₁ idᵛʳ

  -- -- a renaming can also be extended on the right
  -- ᵛʳ⇑ᵛʳ : ∀ {Γ Δ} → Γ ⇒ᵛʳ Δ → ∀ {Ξ} → Ξ ,, Γ ⇒ᵛʳ Ξ ,, Δ
  -- ᵛʳ⇑ᵛʳ ρ = idᵛʳ +₁ ρ


  -- the action of a renaming on terms
  module _ {Θ : MContext} where

    infix 6 [_]ᵛʳ_

    [_]ᵛʳ_ : ∀ {Γ Δ A} → Γ ⇒ᵛʳ Δ → Term Θ Γ A → Term Θ Δ A
    [ ρ ]ᵛʳ (tm-var x) = tm-var (ρ x)
    [ ρ ]ᵛʳ (tm-meta M ts) = tm-meta M (λ i → [ ρ ]ᵛʳ (ts i))
    [ ρ ]ᵛʳ (tm-oper f es) = tm-oper f (λ i → [ ⇑ᵛʳ ρ ]ᵛʳ (es i))

  -- The sum of identities is an identity
  idᵛʳ+idᵛʳ : ∀ {Γ Δ} → idᵛʳ {Γ = Γ} +₁ idᵛʳ {Γ = Δ} ≡ᵛʳ idᵛʳ {Γ = Γ ,, Δ}
  idᵛʳ+idᵛʳ (var-inl x) = refl
  idᵛʳ+idᵛʳ (var-inr y) = refl

  -- The action of a renaming respects equality of terms
  []ᵛʳ-resp-≈ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Γ ⇒ᵛʳ Δ} → s ≈ t → [ ρ ]ᵛʳ s ≈ [ ρ ]ᵛʳ t
  []ᵛʳ-resp-≈ (≈-≡ refl) = ≈-≡ refl
  []ᵛʳ-resp-≈ (≈-meta ξ) = ≈-meta (λ i → []ᵛʳ-resp-≈ (ξ i))
  []ᵛʳ-resp-≈ (≈-oper ξ) = ≈-oper (λ i → []ᵛʳ-resp-≈ (ξ i))

  -- The action of a renaming respects equality of renamings
  []ᵛʳ-resp-≡ᵛʳ : ∀ {Θ Γ Δ A} {ρ τ : Γ ⇒ᵛʳ Δ} {t : Term Θ Γ A} → ρ ≡ᵛʳ τ → [ ρ ]ᵛʳ t ≈ [ τ ]ᵛʳ t
  []ᵛʳ-resp-≡ᵛʳ {t = tm-var x} ξ = ≈-≡ (cong tm-var (ξ x))
  []ᵛʳ-resp-≡ᵛʳ {t = tm-meta M ts} ξ = ≈-meta (λ i → []ᵛʳ-resp-≡ᵛʳ ξ)
  []ᵛʳ-resp-≡ᵛʳ {t = tm-oper f es} ξ = ≈-oper (λ i → []ᵛʳ-resp-≡ᵛʳ (+₁-cong₂ ξ ≡ᵛʳ-refl))

  -- The action of the identity is trival
  [id]ᵛʳ : ∀ {Θ Γ A} {t : Term Θ Γ A} → [ idᵛʳ ]ᵛʳ t ≈ t
  [id]ᵛʳ {t = tm-var x} = ≈-refl
  [id]ᵛʳ {t = tm-meta M ts} = ≈-meta λ i → [id]ᵛʳ
  [id]ᵛʳ {t = tm-oper f es} = ≈-oper λ i → ≈-trans ([]ᵛʳ-resp-≡ᵛʳ idᵛʳ+idᵛʳ) [id]ᵛʳ

  -- Extension respects composition
  ⇑ᵛʳ-∘ᵛʳ : ∀ {Γ Δ Ξ Ψ} {ρ : Γ ⇒ᵛʳ Δ} {τ : Δ ⇒ᵛʳ Ξ} → ⇑ᵛʳ {Ξ = Ψ} (τ ∘ᵛʳ ρ) ≡ᵛʳ (⇑ᵛʳ τ) ∘ᵛʳ (⇑ᵛʳ ρ)
  ⇑ᵛʳ-∘ᵛʳ (var-inl x) = refl
  ⇑ᵛʳ-∘ᵛʳ (var-inr y) = refl

  -- The action of a renaming is functorial
  [∘]ᵛʳ : ∀ {Θ Γ Δ Ξ} {ρ : Γ ⇒ᵛʳ Δ} {τ : Δ ⇒ᵛʳ Ξ} {A} {t : Term Θ Γ A} → [ τ ∘ᵛʳ ρ ]ᵛʳ t ≈ [ τ ]ᵛʳ ([ ρ ]ᵛʳ t)
  [∘]ᵛʳ {t = tm-var x} = ≈-refl
  [∘]ᵛʳ {t = tm-meta M ts} = ≈-meta (λ i → [∘]ᵛʳ)
  [∘]ᵛʳ {t = tm-oper f es} = ≈-oper (λ i → ≈-trans ([]ᵛʳ-resp-≡ᵛʳ ⇑ᵛʳ-∘ᵛʳ) [∘]ᵛʳ)

  -- Forming terms over a given metacontext and sort is functorial in the context
  module _ {Θ : MContext} {A : sort} where
    open Categories.Functor
    open Categories.Category.Instance.Setoids

    Term-Functor : Functor VContexts (Setoids ℓ ℓ)
    Term-Functor =
      record
        { F₀ = λ Γ → Term-setoid Θ Γ A
        ; F₁ = λ ρ → record { _⟨$⟩_ = [ ρ ]ᵛʳ_ ; cong = []ᵛʳ-resp-≈ }
        ; identity = ≈-trans [id]ᵛʳ
        ; homomorphism = λ ξ → ≈-trans ([]ᵛʳ-resp-≈ ξ) [∘]ᵛʳ
        ; F-resp-≈ = λ ζ ξ → ≈-trans ([]ᵛʳ-resp-≡ᵛʳ ζ) ([]ᵛʳ-resp-≈ ξ)
        }
