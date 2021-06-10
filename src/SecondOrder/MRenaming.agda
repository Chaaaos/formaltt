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

  split-sum-terms : ∀ {Θ Ψ Ξ Ω Γ A} {ι : Θ ⇒ᵐʳ Ψ} {μ : Ξ ⇒ᵐʳ Ω} {t : Term (Ξ + Θ) Γ A}
    → [ (μ +₁ ι) ]ᵐʳ t ≈ [ (⇑ᵐʳ μ) ∘ᵐʳ (ᵐʳ⇑ᵐʳ ι) ]ᵐʳ t
  split-sum-terms {t} = []ᵐʳ-resp-≡ᵐʳ split-sum
  
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

