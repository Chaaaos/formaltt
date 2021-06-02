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

module SecondOrder.Renaming
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ

  -- a renaming maps variables between contexts in a type-preserving way
  _⇒ʳ_ : ∀ (Γ Δ : VContext) → Set ℓ
  Γ ⇒ʳ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

  infix 4 _⇒ʳ_

  -- equality of renamings

  _≡ʳ_ : ∀ {Γ Δ} (σ τ : Γ ⇒ʳ Δ) → Set ℓ
  _≡ʳ_ {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≡ τ x

  infixl 3 _≡ʳ_

  ≡ʳ-refl : ∀ {Γ Δ} {ρ : Γ ⇒ʳ Δ} → ρ ≡ʳ ρ
  ≡ʳ-refl = λ x → refl

  ≡ʳ-sym : ∀ {Γ Δ} {ρ ν : Γ ⇒ʳ Δ}
          → ρ ≡ʳ ν
          → ν ≡ʳ ρ
  ≡ʳ-sym eq x = sym (eq x)

  ≡ʳ-trans : ∀ {Γ Δ} {ρ ν γ : Γ ⇒ʳ Δ}
           → ρ ≡ʳ ν
           → ν ≡ʳ γ
           → ρ ≡ʳ γ
  ≡ʳ-trans eq1 eq2 x = trans (eq1 x) (eq2 x)

  -- renamings form a setoid

  renaming-setoid : ∀ (Γ Δ : VContext) → Setoid ℓ ℓ
  renaming-setoid Γ Δ =
    record
      { Carrier = Γ ⇒ʳ Δ
      ;  _≈_ = λ ρ ν → ρ ≡ʳ ν
      ; isEquivalence =
                      record
                        { refl = λ {ρ} x → ≡ʳ-refl {Γ} {Δ} {ρ} x
                        ; sym = ≡ʳ-sym
                        ; trans = ≡ʳ-trans
                        }
      }

  -- the identity renaming

  idʳ : ∀ {Γ : VContext} → Γ ⇒ʳ Γ
  idʳ x = x

  -- composition of renamings
  _∘ʳ_ : ∀ {Γ Δ Ξ} → Δ ⇒ʳ Ξ → Γ ⇒ʳ Δ → Γ ⇒ʳ Ξ
  (σ ∘ʳ ρ) x = σ (ρ x)

  infix 7 _∘ʳ_

  -- composition respects equality
  ∘ʳ-resp-≡ʳ : ∀ {Γ Δ Ξ} {τ₁ τ₂ : Δ ⇒ʳ Ξ} {σ₁ σ₂ : Γ ⇒ʳ Δ} →
                 τ₁ ≡ʳ τ₂ → σ₁ ≡ʳ σ₂ → τ₁ ∘ʳ σ₁ ≡ʳ τ₂ ∘ʳ σ₂
  ∘ʳ-resp-≡ʳ {τ₁ = τ₁} {σ₂ = σ₂} ζ ξ x = trans (cong τ₁ (ξ x)) (ζ (σ₂ x))

  -- the identity is the unit

  identity-leftʳ : ∀ {Γ Δ} {ρ : Γ ⇒ʳ Δ} → idʳ ∘ʳ ρ ≡ʳ ρ
  identity-leftʳ ρ = refl

  identity-rightʳ : ∀ {Γ Δ} {ρ : Γ ⇒ʳ Δ} → ρ ∘ʳ idʳ ≡ʳ ρ
  identity-rightʳ ρ = refl

  -- composition is associative

  assocʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ʳ Δ} {ρ : Δ ⇒ʳ Ξ} {σ : Ξ ⇒ʳ Ψ} →
             (σ ∘ʳ ρ) ∘ʳ τ ≡ʳ σ ∘ʳ (ρ ∘ʳ τ)
  assocʳ x = refl

  sym-assocʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ʳ Δ} {ρ : Δ ⇒ʳ Ξ} {σ : Ξ ⇒ʳ Ψ} →
             σ ∘ʳ (ρ ∘ʳ τ) ≡ʳ (σ ∘ʳ ρ) ∘ʳ τ
  sym-assocʳ x = refl

  -- contexts and renamings form a category
  module _ where
    open Categories.Category

    VContexts : Category ℓ ℓ ℓ
    VContexts =
      record
        { Obj = VContext
        ; _⇒_ = _⇒ʳ_
        ; _≈_ = _≡ʳ_
        ; id = idʳ
        ; _∘_ = _∘ʳ_
        ; assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → assocʳ {τ = f} {ρ = g} {σ = h}
        ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → sym-assocʳ {τ = f} {ρ = g} {σ = h}
        ; identityˡ = λ x → refl
        ; identityʳ = λ x → refl
        ; identity² = λ x → refl
        ; equiv = record { refl = λ {ρ} {_} → ≡ʳ-refl {ρ = ρ} ; sym = ≡ʳ-sym ; trans = ≡ʳ-trans }
        ; ∘-resp-≈ = ∘ʳ-resp-≡ʳ
        }


  -- the coproduct structure of the category
  module _ where

    infixl 7 [_,_]ʳ

    [_,_]ʳ : ∀ {Γ Δ Ξ} → Γ ⇒ʳ Ξ → Δ ⇒ʳ Ξ → Γ ,, Δ ⇒ʳ Ξ
    [ σ , τ ]ʳ (var-inl x) = σ x
    [ σ , τ ]ʳ (var-inr y) = τ y

    inlʳ : ∀ {Γ Δ} → Γ ⇒ʳ Γ ,, Δ
    inlʳ = var-inl

    inrʳ : ∀ {Γ Δ} → Δ ⇒ʳ Γ ,, Δ
    inrʳ = var-inr

    uniqueʳ : ∀ {Γ Δ Ξ} {τ : Γ ,, Δ ⇒ʳ Ξ} {ρ : Γ ⇒ʳ Ξ} {σ : Δ ⇒ʳ Ξ}
              → τ ∘ʳ inlʳ ≡ʳ ρ
              → τ ∘ʳ inrʳ ≡ʳ σ
              → [ ρ , σ ]ʳ ≡ʳ τ
    uniqueʳ ξ ζ (var-inl x) = sym (ξ x)
    uniqueʳ ξ ζ (var-inr y) = sym (ζ y)

    Context-+ : Categories.Category.Cocartesian.BinaryCoproducts VContexts
    Context-+ =
      record {
        coproduct =
          λ {Γ Δ} →
          record
            { A+B = Γ ,, Δ
            ; i₁ = inlʳ
            ; i₂ = inrʳ
            ; [_,_] = [_,_]ʳ
            ; inject₁ = λ x → refl
            ; inject₂ = λ x → refl
            ; unique = uniqueʳ
            }
      }

  open Categories.Category.Cocartesian.BinaryCoproducts Context-+

  -- the renaming from the empty context

  inʳ : ∀ {Γ} → ctx-empty ⇒ʳ Γ
  inʳ ()

  -- extension of a renaming is summing with identity
  ⇑ʳ : ∀ {Γ Δ Ξ} → Γ ⇒ʳ Δ → Γ ,, Ξ ⇒ʳ Δ ,, Ξ
  ⇑ʳ ρ = ρ +₁ idʳ

  -- a renaming can also be extended on the right
  ʳ⇑ʳ : ∀ {Γ Δ} → Γ ⇒ʳ Δ → ∀ {Ξ} → Ξ ,, Γ ⇒ʳ Ξ ,, Δ
  ʳ⇑ʳ ρ = idʳ +₁ ρ


  -- the action of a renaming on terms
  module _ {Θ : MContext} where

    infix 6 [_]ʳ_

    [_]ʳ_ : ∀ {Γ Δ A} → Γ ⇒ʳ Δ → Term Θ Γ A → Term Θ Δ A
    [ ρ ]ʳ (tm-var x) = tm-var (ρ x)
    [ ρ ]ʳ (tm-meta M ts) = tm-meta M (λ i → [ ρ ]ʳ (ts i))
    [ ρ ]ʳ (tm-oper f es) = tm-oper f (λ i → [ ⇑ʳ ρ ]ʳ (es i))

  -- The sum of identities is an identity
  idʳ+idʳ : ∀ {Γ Δ} → idʳ {Γ = Γ} +₁ idʳ {Γ = Δ} ≡ʳ idʳ {Γ = Γ ,, Δ}
  idʳ+idʳ (var-inl x) = refl
  idʳ+idʳ (var-inr y) = refl

  -- The action of a renaming respects equality of terms
  []ʳ-resp-≈ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Γ ⇒ʳ Δ} → s ≈ t → [ ρ ]ʳ s ≈ [ ρ ]ʳ t
  []ʳ-resp-≈ (≈-≡ refl) = ≈-≡ refl
  []ʳ-resp-≈ (≈-meta ξ) = ≈-meta (λ i → []ʳ-resp-≈ (ξ i))
  []ʳ-resp-≈ (≈-oper ξ) = ≈-oper (λ i → []ʳ-resp-≈ (ξ i))

  -- The action of a renaming respects equality of renamings
  []ʳ-resp-≡ʳ : ∀ {Θ Γ Δ A} {ρ τ : Γ ⇒ʳ Δ} {t : Term Θ Γ A} → ρ ≡ʳ τ → [ ρ ]ʳ t ≈ [ τ ]ʳ t
  []ʳ-resp-≡ʳ {t = tm-var x} ξ = ≈-≡ (cong tm-var (ξ x))
  []ʳ-resp-≡ʳ {t = tm-meta M ts} ξ = ≈-meta (λ i → []ʳ-resp-≡ʳ ξ)
  []ʳ-resp-≡ʳ {t = tm-oper f es} ξ = ≈-oper (λ i → []ʳ-resp-≡ʳ (+₁-cong₂ ξ ≡ʳ-refl))

  -- The action of the identity is trival
  [id]ʳ : ∀ {Θ Γ A} {t : Term Θ Γ A} → [ idʳ ]ʳ t ≈ t
  [id]ʳ {t = tm-var x} = ≈-refl
  [id]ʳ {t = tm-meta M ts} = ≈-meta λ i → [id]ʳ
  [id]ʳ {t = tm-oper f es} = ≈-oper λ i → ≈-trans ([]ʳ-resp-≡ʳ idʳ+idʳ) [id]ʳ

  -- Extension respects composition
  ⇑ʳ-∘ʳ : ∀ {Γ Δ Ξ Ψ} {ρ : Γ ⇒ʳ Δ} {τ : Δ ⇒ʳ Ξ} → ⇑ʳ {Ξ = Ψ} (τ ∘ʳ ρ) ≡ʳ (⇑ʳ τ) ∘ʳ (⇑ʳ ρ)
  ⇑ʳ-∘ʳ (var-inl x) = refl
  ⇑ʳ-∘ʳ (var-inr y) = refl

  -- The action of a renaming is functorial
  [∘]ʳ : ∀ {Θ Γ Δ Ξ} {ρ : Γ ⇒ʳ Δ} {τ : Δ ⇒ʳ Ξ} {A} {t : Term Θ Γ A} → [ τ ∘ʳ ρ ]ʳ t ≈ [ τ ]ʳ ([ ρ ]ʳ t)
  [∘]ʳ {t = tm-var x} = ≈-refl
  [∘]ʳ {t = tm-meta M ts} = ≈-meta (λ i → [∘]ʳ)
  [∘]ʳ {t = tm-oper f es} = ≈-oper (λ i → ≈-trans ([]ʳ-resp-≡ʳ ⇑ʳ-∘ʳ) [∘]ʳ)

  -- Forming terms over a given metacontext and sort is functorial in the context
  module _ {Θ : MContext} {A : sort} where
    open Categories.Functor
    open Categories.Category.Instance.Setoids

    Term-Functor : Functor VContexts (Setoids ℓ ℓ)
    Term-Functor =
      record
        { F₀ = λ Γ → Term-setoid Θ Γ A
        ; F₁ = λ ρ → record { _⟨$⟩_ = [ ρ ]ʳ_ ; cong = []ʳ-resp-≈ }
        ; identity = ≈-trans [id]ʳ
        ; homomorphism = λ ξ → ≈-trans ([]ʳ-resp-≈ ξ) [∘]ʳ
        ; F-resp-≈ = λ ζ ξ → ≈-trans ([]ʳ-resp-≡ʳ ζ) ([]ʳ-resp-≈ ξ)
        }
