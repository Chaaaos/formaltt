open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)
import Function.Equality
import Relation.Binary.Reasoning.Setoid as SetoidR

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
  _⇒ᵛ_ : ∀ (Γ Δ : VContext) → Set ℓ
  Γ ⇒ᵛ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

  infix 4 _⇒ᵛ_

  -- equality of renamings

  _≡ᵛ_ : ∀ {Γ Δ} (σ τ : Γ ⇒ᵛ Δ) → Set ℓ
  _≡ᵛ_ {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≡ τ x

  infixl 3 _≡ᵛ_

  ≡ᵛ-refl : ∀ {Γ Δ} {ρ : Γ ⇒ᵛ Δ} → ρ ≡ᵛ ρ
  ≡ᵛ-refl = λ x → refl

  ≡ᵛ-sym : ∀ {Γ Δ} {ρ ν : Γ ⇒ᵛ Δ}
          → ρ ≡ᵛ ν
          → ν ≡ᵛ ρ
  ≡ᵛ-sym eq x = sym (eq x)

  ≡ᵛ-trans : ∀ {Γ Δ} {ρ ν γ : Γ ⇒ᵛ Δ}
           → ρ ≡ᵛ ν
           → ν ≡ᵛ γ
           → ρ ≡ᵛ γ
  ≡ᵛ-trans eq1 eq2 x = trans (eq1 x) (eq2 x)

  -- renamings form a setoid

  renaming-setoid : ∀ (Γ Δ : VContext) → Setoid ℓ ℓ
  renaming-setoid Γ Δ =
    record
      { Carrier = Γ ⇒ᵛ Δ
      ;  _≈_ = λ ρ ν → ρ ≡ᵛ ν
      ; isEquivalence =
                      record
                        { refl = λ {ρ} x → ≡ᵛ-refl {Γ} {Δ} {ρ} x
                        ; sym = ≡ᵛ-sym
                        ; trans = ≡ᵛ-trans
                        }
      }

  -- renaming preserves equality of variables
  ρ-resp-≡ : ∀ {Γ Δ A} {x y : A ∈ Γ} {ρ : Γ ⇒ᵛ Δ} → x ≡ y → ρ x ≡ ρ y
  ρ-resp-≡ refl = refl

  -- the identity renaming

  idᵛ : ∀ {Γ : VContext} → Γ ⇒ᵛ Γ
  idᵛ x = x

  -- composition of renamings
  _∘ᵛ_ : ∀ {Γ Δ Ξ} → Δ ⇒ᵛ Ξ → Γ ⇒ᵛ Δ → Γ ⇒ᵛ Ξ
  (σ ∘ᵛ ρ) x = σ (ρ x)

  infix 7 _∘ᵛ_

  -- composition respects equality
  ∘ᵛ-resp-≡ᵛ : ∀ {Γ Δ Ξ} {τ₁ τ₂ : Δ ⇒ᵛ Ξ} {σ₁ σ₂ : Γ ⇒ᵛ Δ} →
                 τ₁ ≡ᵛ τ₂ → σ₁ ≡ᵛ σ₂ → τ₁ ∘ᵛ σ₁ ≡ᵛ τ₂ ∘ᵛ σ₂
  ∘ᵛ-resp-≡ᵛ {τ₁ = τ₁} {σ₂ = σ₂} ζ ξ x = trans (cong τ₁ (ξ x)) (ζ (σ₂ x))

  -- the identity is the unit

  identity-leftᵛ : ∀ {Γ Δ} {ρ : Γ ⇒ᵛ Δ} → idᵛ ∘ᵛ ρ ≡ᵛ ρ
  identity-leftᵛ ρ = refl

  identity-rightᵛ : ∀ {Γ Δ} {ρ : Γ ⇒ᵛ Δ} → ρ ∘ᵛ idᵛ ≡ᵛ ρ
  identity-rightᵛ ρ = refl

  -- composition is associative

  assocᵛ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ᵛ Δ} {ρ : Δ ⇒ᵛ Ξ} {σ : Ξ ⇒ᵛ Ψ} →
             (σ ∘ᵛ ρ) ∘ᵛ τ ≡ᵛ σ ∘ᵛ (ρ ∘ᵛ τ)
  assocᵛ x = refl

  sym-assocᵛ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ᵛ Δ} {ρ : Δ ⇒ᵛ Ξ} {σ : Ξ ⇒ᵛ Ψ} →
             σ ∘ᵛ (ρ ∘ᵛ τ) ≡ᵛ (σ ∘ᵛ ρ) ∘ᵛ τ
  sym-assocᵛ x = refl

  -- contexts and renamings form a category
  module _ where
    open Categories.Category

    VContexts : Category ℓ ℓ ℓ
    VContexts =
      record
        { Obj = VContext
        ; _⇒_ = _⇒ᵛ_
        ; _≈_ = _≡ᵛ_
        ; id = idᵛ
        ; _∘_ = _∘ᵛ_
        ; assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → assocᵛ {τ = f} {ρ = g} {σ = h}
        ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → sym-assocᵛ {τ = f} {ρ = g} {σ = h}
        ; identityˡ = λ x → refl
        ; identityʳ = λ x → refl
        ; identity² = λ x → refl
        ; equiv = record { refl = λ {ρ} {_} → ≡ᵛ-refl {ρ = ρ} ; sym = ≡ᵛ-sym ; trans = ≡ᵛ-trans }
        ; ∘-resp-≈ = ∘ᵛ-resp-≡ᵛ
        }


  -- the coproduct structure of the category
  module _ where

    infixl 7 [_,_]ᵛ

    [_,_]ᵛ : ∀ {Γ Δ Ξ} → Γ ⇒ᵛ Ξ → Δ ⇒ᵛ Ξ → Γ ,, Δ ⇒ᵛ Ξ
    [ σ , τ ]ᵛ (var-inl x) = σ x
    [ σ , τ ]ᵛ (var-inr y) = τ y

    [,]ᵛ-resp-≡ᵛ : ∀ {Γ Δ Ξ} {ρ₁ ρ₂ : Γ ⇒ᵛ Ξ} {τ₁ τ₂ : Δ ⇒ᵛ Ξ} → ρ₁ ≡ᵛ ρ₂ → τ₁ ≡ᵛ τ₂ → [ ρ₁ , τ₁ ]ᵛ ≡ᵛ [ ρ₂ , τ₂ ]ᵛ
    [,]ᵛ-resp-≡ᵛ pρ pτ (var-inl x) = pρ x
    [,]ᵛ-resp-≡ᵛ pρ pτ (var-inr x) = pτ x

    inlᵛ : ∀ {Γ Δ} → Γ ⇒ᵛ Γ ,, Δ
    inlᵛ = var-inl

    inrᵛ : ∀ {Γ Δ} → Δ ⇒ᵛ Γ ,, Δ
    inrᵛ = var-inr

    uniqueᵛ : ∀ {Γ Δ Ξ} {τ : Γ ,, Δ ⇒ᵛ Ξ} {ρ : Γ ⇒ᵛ Ξ} {σ : Δ ⇒ᵛ Ξ}
              → τ ∘ᵛ inlᵛ ≡ᵛ ρ
              → τ ∘ᵛ inrᵛ ≡ᵛ σ
              → [ ρ , σ ]ᵛ ≡ᵛ τ
    uniqueᵛ ξ ζ (var-inl x) = sym (ξ x)
    uniqueᵛ ξ ζ (var-inr y) = sym (ζ y)

    uniqueᵛ² : ∀ {Γ Δ Ξ} {τ σ : Γ ,, Δ ⇒ᵛ Ξ}
              → τ ∘ᵛ inlᵛ ≡ᵛ σ ∘ᵛ inlᵛ
              → τ ∘ᵛ inrᵛ ≡ᵛ σ ∘ᵛ inrᵛ
              → τ ≡ᵛ σ
    uniqueᵛ² ξ ζ (var-inl x) = ξ x
    uniqueᵛ² ξ ζ (var-inr y) = ζ y

    Context-+ : Categories.Category.Cocartesian.BinaryCoproducts VContexts
    Context-+ =
      record {
        coproduct =
          λ {Γ Δ} →
          record
            { A+B = Γ ,, Δ
            ; i₁ = inlᵛ
            ; i₂ = inrᵛ
            ; [_,_] = [_,_]ᵛ
            ; inject₁ = λ x → refl
            ; inject₂ = λ x → refl
            ; unique = uniqueᵛ
            }
      }

  open Categories.Category.Cocartesian.BinaryCoproducts Context-+

  -- the renaming from the empty context

  inᵛ : ∀ {Γ} → ctx-empty ⇒ᵛ Γ
  inᵛ ()

  -- extension of a renaming is summing with identity
  ⇑ᵛ : ∀ {Γ Δ Ξ} → Γ ⇒ᵛ Δ → Γ ,, Ξ ⇒ᵛ Δ ,, Ξ
  ⇑ᵛ ρ = ρ +₁ idᵛ

  -- a renaming can also be extended on the right
  ʳ⇑ᵛ : ∀ {Γ Δ} → Γ ⇒ᵛ Δ → ∀ {Ξ} → Ξ ,, Γ ⇒ᵛ Ξ ,, Δ
  ʳ⇑ᵛ ρ = idᵛ +₁ ρ

  -- right extension of renamings commutes with right injection
  ʳ⇑ᵛ-comm-inrᵛ : ∀ {Γ Δ Ξ} (ρ : Γ ⇒ᵛ Δ)
    → (ʳ⇑ᵛ ρ {Ξ = Ξ}) ∘ᵛ (inrᵛ {Δ = Γ}) ≡ᵛ inrᵛ ∘ᵛ ρ
  ʳ⇑ᵛ-comm-inrᵛ ρ var-slot = refl
  ʳ⇑ᵛ-comm-inrᵛ ρ (var-inl x) = refl
  ʳ⇑ᵛ-comm-inrᵛ ρ (var-inr x) = refl

  -- left extension of renamings commutes with left injection
  ⇑ᵛ-comm-inlᵛ : ∀ {Γ Δ Ξ} (ρ : Γ ⇒ᵛ Δ) → (⇑ᵛ {Ξ = Ξ} ρ) ∘ᵛ (inlᵛ {Δ = Ξ}) ≡ᵛ inlᵛ ∘ᵛ ρ
  ⇑ᵛ-comm-inlᵛ ρ var-slot = refl
  ⇑ᵛ-comm-inlᵛ ρ (var-inl x) = refl
  ⇑ᵛ-comm-inlᵛ ρ (var-inr x) = refl

  -- the action of a renaming on terms
  module _ {Θ : MContext} where

    infix 6 [_]ᵛ_

    [_]ᵛ_ : ∀ {Γ Δ A} → Γ ⇒ᵛ Δ → Term Θ Γ A → Term Θ Δ A
    [ ρ ]ᵛ (tm-var x) = tm-var (ρ x)
    [ ρ ]ᵛ (tm-meta M ts) = tm-meta M (λ i → [ ρ ]ᵛ (ts i))
    [ ρ ]ᵛ (tm-oper f es) = tm-oper f (λ i → [ ⇑ᵛ ρ ]ᵛ (es i))

  -- The sum of identities is an identity
  idᵛ+idᵛ : ∀ {Γ Δ} → idᵛ {Γ = Γ} +₁ idᵛ {Γ = Δ} ≡ᵛ idᵛ {Γ = Γ ,, Δ}
  idᵛ+idᵛ (var-inl x) = refl
  idᵛ+idᵛ (var-inr y) = refl

  -- The action of a renaming respects equality of terms
  []ᵛ-resp-≈ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Γ ⇒ᵛ Δ} → s ≈ t → [ ρ ]ᵛ s ≈ [ ρ ]ᵛ t
  []ᵛ-resp-≈ (≈-≡ refl) = ≈-≡ refl
  []ᵛ-resp-≈ (≈-meta ξ) = ≈-meta (λ i → []ᵛ-resp-≈ (ξ i))
  []ᵛ-resp-≈ (≈-oper ξ) = ≈-oper (λ i → []ᵛ-resp-≈ (ξ i))

  -- The action of a renaming respects equality of renamings
  []ᵛ-resp-≡ᵛ : ∀ {Θ Γ Δ A} {ρ τ : Γ ⇒ᵛ Δ} {t : Term Θ Γ A} → ρ ≡ᵛ τ → [ ρ ]ᵛ t ≈ [ τ ]ᵛ t
  []ᵛ-resp-≡ᵛ {t = tm-var x} ξ = ≈-≡ (cong tm-var (ξ x))
  []ᵛ-resp-≡ᵛ {t = tm-meta M ts} ξ = ≈-meta (λ i → []ᵛ-resp-≡ᵛ ξ)
  []ᵛ-resp-≡ᵛ {t = tm-oper f es} ξ = ≈-oper (λ i → []ᵛ-resp-≡ᵛ (+₁-cong₂ ξ ≡ᵛ-refl))

  -- The action of the identity is trival
  [idᵛ] : ∀ {Θ Γ A} {t : Term Θ Γ A} → [ idᵛ ]ᵛ t ≈ t
  [idᵛ] {t = tm-var x} = ≈-refl
  [idᵛ] {t = tm-meta M ts} = ≈-meta λ i → [idᵛ]
  [idᵛ] {t = tm-oper f es} = ≈-oper λ i → ≈-trans ([]ᵛ-resp-≡ᵛ idᵛ+idᵛ) [idᵛ]

  -- Extension respects composition
  ⇑ᵛ-resp-∘ᵛ : ∀ {Γ Δ Ξ Ψ} {ρ : Γ ⇒ᵛ Δ} {τ : Δ ⇒ᵛ Ξ} → ⇑ᵛ {Ξ = Ψ} (τ ∘ᵛ ρ) ≡ᵛ (⇑ᵛ τ) ∘ᵛ (⇑ᵛ ρ)
  ⇑ᵛ-resp-∘ᵛ (var-inl x) = refl
  ⇑ᵛ-resp-∘ᵛ (var-inr y) = refl

  -- Right extension respects composition
  ʳ⇑ᵛ-resp-∘ᵛ : ∀ {Γ Δ Ξ Ψ} {ρ : Γ ⇒ᵛ Δ} {τ : Δ ⇒ᵛ Ξ} → ʳ⇑ᵛ (τ ∘ᵛ ρ) {Ξ = Ψ} ≡ᵛ (ʳ⇑ᵛ τ) ∘ᵛ (ʳ⇑ᵛ ρ)
  ʳ⇑ᵛ-resp-∘ᵛ (var-inl x) = refl
  ʳ⇑ᵛ-resp-∘ᵛ (var-inr y) = refl

  -- The action of a renaming is functorial
  [∘ᵛ] : ∀ {Θ Γ Δ Ξ} {ρ : Γ ⇒ᵛ Δ} {τ : Δ ⇒ᵛ Ξ} {A} {t : Term Θ Γ A}
    → [ τ ∘ᵛ ρ ]ᵛ t ≈ [ τ ]ᵛ ([ ρ ]ᵛ t)
  [∘ᵛ] {t = tm-var x} = ≈-refl
  [∘ᵛ] {t = tm-meta M ts} = ≈-meta (λ i → [∘ᵛ])
  [∘ᵛ] {t = tm-oper f es} = ≈-oper (λ i → ≈-trans ([]ᵛ-resp-≡ᵛ ⇑ᵛ-resp-∘ᵛ) [∘ᵛ])

  ∘ᵛ-resp-ʳ⇑ᵛ : ∀ {Γ Δ Ξ Λ} {ρ : Γ ⇒ᵛ Δ} {τ : Δ ⇒ᵛ Ξ}
    → ʳ⇑ᵛ (τ ∘ᵛ ρ) {Ξ = Λ} ≡ᵛ ʳ⇑ᵛ τ ∘ᵛ ʳ⇑ᵛ ρ
  ∘ᵛ-resp-ʳ⇑ᵛ (var-inl x) = refl
  ∘ᵛ-resp-ʳ⇑ᵛ (var-inr y) = refl

  ∘ᵛ-resp-ʳ⇑ᵛ-term : ∀ {Θ Γ Δ Ξ Λ A} {ρ : Γ ⇒ᵛ Δ} {τ : Δ ⇒ᵛ Ξ} {t : Term Θ (Λ ,, Γ) A}
    → [ ʳ⇑ᵛ (τ ∘ᵛ ρ) {Ξ = Λ} ]ᵛ t ≈ [ ʳ⇑ᵛ τ ]ᵛ ([ ʳ⇑ᵛ ρ ]ᵛ t)
  ∘ᵛ-resp-ʳ⇑ᵛ-term {Θ} {Γ} {Δ} {Ξ} {Λ} {A} {ρ} {τ} {t = t} =
    let open SetoidR (Term-setoid Θ (Λ ,, Ξ) A) in
    begin
    [ ʳ⇑ᵛ (τ ∘ᵛ ρ) {Ξ = Λ} ]ᵛ t ≈⟨ []ᵛ-resp-≡ᵛ ∘ᵛ-resp-ʳ⇑ᵛ ⟩
    [ ʳ⇑ᵛ τ ∘ᵛ ʳ⇑ᵛ ρ ]ᵛ t ≈⟨ [∘ᵛ] ⟩
    [ ʳ⇑ᵛ τ ]ᵛ ([ ʳ⇑ᵛ ρ ]ᵛ t)
    ∎

  ʳ⇑ᵛ-comm-inrᵛ-term : ∀ {Θ Γ Δ Ξ A} {ρ : Γ ⇒ᵛ Δ} {t : Term Θ Γ A}
    → ([ ʳ⇑ᵛ ρ {Ξ = Ξ} ]ᵛ ([ inrᵛ {Δ = Γ} ]ᵛ t)) ≈ ([ inrᵛ ]ᵛ ([ ρ ]ᵛ t))
  ʳ⇑ᵛ-comm-inrᵛ-term {Θ} {Γ} {Δ} {Ξ} {A} {ρ} {t = t} =
    let open SetoidR (Term-setoid Θ (Ξ ,, Δ) A) in
    begin
    [ ʳ⇑ᵛ ρ ]ᵛ ([ inrᵛ ]ᵛ t) ≈⟨ ≈-sym [∘ᵛ] ⟩
    [ ʳ⇑ᵛ ρ ∘ᵛ var-inr ]ᵛ t ≈⟨ []ᵛ-resp-≡ᵛ (ʳ⇑ᵛ-comm-inrᵛ ρ) ⟩
    [ inrᵛ ∘ᵛ ρ ]ᵛ t ≈⟨ [∘ᵛ] ⟩
    [ inrᵛ ]ᵛ ([ ρ ]ᵛ t)
    ∎

  -- Forming terms over a given metacontext and sort is functorial in the context
  module _ {Θ : MContext} {A : sort} where
    open Categories.Functor
    open Categories.Category.Instance.Setoids

    Term-Functor : Functor VContexts (Setoids ℓ ℓ)
    Term-Functor =
      record
        { F₀ = λ Γ → Term-setoid Θ Γ A
        ; F₁ = λ ρ → record { _⟨$⟩_ = [ ρ ]ᵛ_ ; cong = []ᵛ-resp-≈ }
        ; identity = ≈-trans [idᵛ]
        ; homomorphism = λ ξ → ≈-trans ([]ᵛ-resp-≈ ξ) [∘ᵛ]
        ; F-resp-≈ = λ ζ ξ → ≈-trans ([]ᵛ-resp-≡ᵛ ζ) ([]ᵛ-resp-≈ ξ)
        }
