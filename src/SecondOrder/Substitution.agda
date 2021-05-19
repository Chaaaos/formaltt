open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid; cong; trans)
import Function.Equality

import Categories.Category
import Categories.Functor
import Categories.Category.Instance.Setoids
import Categories.Monad.Relative
import Categories.Category.Cocartesian

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Renaming
import SecondOrder.Term
import SecondOrder.IndexedCategory
import SecondOrder.RelativeKleisli

module SecondOrder.Substitution
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.Renaming Σ

  -- substitution

  infix 4 _⊕_⇒ˢ_

  _⊕_⇒ˢ_ : ∀ (Θ : MetaContext) (Γ Δ : Context) → Set ℓ
  Θ ⊕ Γ ⇒ˢ Δ = ∀ {A} (x : A ∈ Γ) → Term Θ Δ A

  -- syntactic equality of substitutions

  infix 5 _≈ˢ_

  _≈ˢ_ : ∀ {Θ} {Γ Δ} (σ τ : Θ ⊕ Γ ⇒ˢ Δ) → Set ℓ
  _≈ˢ_ {Θ} {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≈ τ x

  -- extension of a substitution

  ⇑ˢ : ∀ {Θ Γ Δ Ξ} → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ (Γ ,, Ξ) ⇒ˢ (Δ ,, Ξ)
  ⇑ˢ σ (var-inl x) = [ var-inl ]ʳ σ x
  ⇑ˢ σ (var-inr y) = tm-var (var-inr y)

  -- extension respects equality of substitutions

  ⇑ˢ-resp-≈ˢ : ∀ {Θ Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒ˢ Δ} → σ ≈ˢ τ → ⇑ˢ {Ξ = Ξ} σ ≈ˢ ⇑ˢ {Ξ = Ξ} τ
  ⇑ˢ-resp-≈ˢ ξ (var-inl x) = []ʳ-resp-≈ (ξ x)
  ⇑ˢ-resp-≈ˢ ξ (var-inr y) = ≈-refl

  -- the action of a renaming on a substitution

  infixr 6 _ʳ∘ˢ_

  _ʳ∘ˢ_ : ∀ {Θ} {Γ Δ Ξ} (ρ : Δ ⇒ʳ Ξ) (σ : Θ ⊕ Γ ⇒ˢ Δ) → Θ ⊕ Γ ⇒ˢ Ξ
  (ρ ʳ∘ˢ σ) x =  [ ρ ]ʳ (σ x)

  infixl 6 _ˢ∘ʳ_

  _ˢ∘ʳ_ : ∀ {Θ} {Γ Δ Ξ} (σ : Θ ⊕ Δ ⇒ˢ Ξ) (ρ : Γ ⇒ʳ Δ)  → Θ ⊕ Γ ⇒ˢ Ξ
  (σ ˢ∘ʳ ρ) x =  σ (ρ x)

  -- extension commutes with renaming action

  ⇑ˢ-ˢ∘ʳ : ∀ {Θ} {Γ Δ Ξ Ψ} {ρ : Γ ⇒ʳ Δ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} → ⇑ˢ {Ξ = Ψ} (σ ˢ∘ʳ ρ) ≈ˢ ⇑ˢ σ ˢ∘ʳ ⇑ʳ ρ
  ⇑ˢ-ˢ∘ʳ (var-inl x) = ≈-refl
  ⇑ˢ-ˢ∘ʳ (var-inr x) = ≈-refl

  -- the action of a substitution on a term

  infixr 6 [_]ˢ_

  [_]ˢ_ : ∀ {Θ Γ Δ A} → Θ ⊕ Γ ⇒ˢ Δ → Term Θ Γ A → Term Θ Δ A
  [ σ ]ˢ (tm-var x) = σ x
  [ σ ]ˢ (tm-meta M ts) = tm-meta M (λ i → [ σ ]ˢ ts i)
  [ σ ]ˢ (tm-oper f es) = tm-oper f (λ i → [ ⇑ˢ σ ]ˢ es i)

  -- composition of substitutions

  infixl 7 _∘ˢ_
  _∘ˢ_ : ∀ {Θ} {Γ Δ Ξ} → Θ ⊕ Δ ⇒ˢ Ξ → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ Γ ⇒ˢ Ξ
  (σ ∘ˢ τ) x = [ σ ]ˢ τ x

  -- substitution action respects equality of terms

  []ˢ-resp-≈ : ∀ {Θ} {Γ Δ} {A} (σ : Θ ⊕ Γ ⇒ˢ Δ) {t u : Term Θ Γ A} → t ≈ u → [ σ ]ˢ t ≈  [ σ ]ˢ u
  []ˢ-resp-≈ σ (≈-≡ refl) = ≈-refl
  []ˢ-resp-≈ σ (≈-meta ξ) = ≈-meta (λ i → []ˢ-resp-≈ σ (ξ i))
  []ˢ-resp-≈ σ (≈-oper ξ) = ≈-oper (λ i → []ˢ-resp-≈ (⇑ˢ σ) (ξ i))

  -- substitution action respects equality of substitutions

  []ˢ-resp-≈ˢ : ∀ {Θ} {Γ Δ} {A} {σ τ : Θ ⊕ Γ ⇒ˢ Δ} (t : Term Θ Γ A) → σ ≈ˢ τ → [ σ ]ˢ t ≈ [ τ ]ˢ t
  []ˢ-resp-≈ˢ (tm-var x) ξ = ξ x
  []ˢ-resp-≈ˢ (tm-meta M ts) ξ = ≈-meta (λ i → []ˢ-resp-≈ˢ (ts i) ξ)
  []ˢ-resp-≈ˢ (tm-oper f es) ξ = ≈-oper (λ i → []ˢ-resp-≈ˢ (es i) (⇑ˢ-resp-≈ˢ ξ))

  -- substitution actions respects both equalities

  []ˢ-resp-≈ˢ-≈ : ∀ {Θ} {Γ Δ} {A} {σ τ : Θ ⊕ Γ ⇒ˢ Δ} {t u : Term Θ Γ A} → σ ≈ˢ τ → t ≈ u → [ σ ]ˢ t ≈ [ τ ]ˢ u
  []ˢ-resp-≈ˢ-≈ {τ = τ} {t = t} ζ ξ = ≈-trans ([]ˢ-resp-≈ˢ t ζ) ([]ˢ-resp-≈ τ ξ)

  -- identity substitution

  idˢ : ∀ {Θ Γ} → Θ ⊕ Γ ⇒ˢ Γ
  idˢ = tm-var

  -- extension preserves identity

  ⇑ˢ-idˢ : ∀ {Θ} {Γ Δ} → ⇑ˢ idˢ ≈ˢ idˢ {Θ = Θ} {Γ = Γ ,, Δ}
  ⇑ˢ-idˢ (var-inl x) = ≈-refl
  ⇑ˢ-idˢ (var-inr y) = ≈-refl

  -- the identity substution acts trivially

  [id]ˢ : ∀ {Θ} {Γ} {A} {t : Term Θ Γ A} → [ idˢ ]ˢ t ≈ t
  [id]ˢ {t = tm-var x} = ≈-refl
  [id]ˢ {t = tm-meta M ts} = ≈-meta (λ i → [id]ˢ)
  [id]ˢ {t = tm-oper f es} = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) ⇑ˢ-idˢ) [id]ˢ)

  -- interaction of extension and right renaming action

  [⇑ˢ∘ʳ] : ∀ {Θ} {A} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} {ρ : Γ ⇒ʳ Δ} (t : Term Θ (Γ ,, Ψ) A) →
         [ ⇑ˢ (σ ˢ∘ʳ ρ) ]ˢ t ≈ [ ⇑ˢ σ ]ˢ [ ⇑ʳ ρ ]ʳ t
  [⇑ˢ∘ʳ] (tm-var (var-inl x)) = ≈-refl
  [⇑ˢ∘ʳ] (tm-var (var-inr x)) = ≈-refl
  [⇑ˢ∘ʳ] (tm-meta M ts) = ≈-meta (λ i → [⇑ˢ∘ʳ] (ts i))
  [⇑ˢ∘ʳ] (tm-oper f es) = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) (⇑ˢ-resp-≈ˢ ⇑ˢ-ˢ∘ʳ)) ([⇑ˢ∘ʳ] (es i)))

  -- interaction of extension and left renaming action

  ⇑ˢ-ʳ∘ˢ : ∀ {Θ} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {ρ : Δ ⇒ʳ Ξ} →
           ⇑ˢ {Ξ = Ψ} (ρ ʳ∘ˢ σ) ≈ˢ ⇑ʳ ρ ʳ∘ˢ ⇑ˢ σ
  ⇑ˢ-ʳ∘ˢ (var-inl x) = ≈-trans (≈-sym [∘]ʳ) (≈-trans ([]ʳ-resp-≡ʳ (λ _ → refl)) [∘]ʳ)
  ⇑ˢ-ʳ∘ˢ (var-inr y) = ≈-refl

  [⇑ʳ∘ˢ] : ∀ {Θ} {A} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {ρ : Δ ⇒ʳ Ξ} (t : Term Θ (Γ ,, Ψ) A) →
         [ ⇑ˢ (ρ ʳ∘ˢ σ) ]ˢ t ≈ [ ⇑ʳ ρ ]ʳ ([ ⇑ˢ σ ]ˢ t)
  [⇑ʳ∘ˢ] (tm-var x) = ⇑ˢ-ʳ∘ˢ x
  [⇑ʳ∘ˢ] (tm-meta M ts) = ≈-meta (λ i → [⇑ʳ∘ˢ] (ts i))
  [⇑ʳ∘ˢ] (tm-oper f es) = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) (⇑ˢ-resp-≈ˢ ⇑ˢ-ʳ∘ˢ)) ([⇑ʳ∘ˢ] (es i)))

  -- functoriality of left renaming action

  [ʳ∘ˢ]ˢ : ∀ {Θ} {A} {Γ Δ Ξ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {ρ : Δ ⇒ʳ Ξ} (t : Term Θ Γ A) →
           [ ρ ʳ∘ˢ σ ]ˢ t ≈ [ ρ ]ʳ ([ σ ]ˢ t)
  [ʳ∘ˢ]ˢ (tm-var x) = ≈-refl
  [ʳ∘ˢ]ˢ (tm-meta M ts) = ≈-meta (λ i → [ʳ∘ˢ]ˢ (ts i))
  [ʳ∘ˢ]ˢ (tm-oper f es) = ≈-oper (λ i → [⇑ʳ∘ˢ] (es i))

  -- functoriality of right renaming action

  [ˢ∘ʳ]ˢ : ∀ {Θ} {A} {Γ Δ Ξ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} {ρ : Γ ⇒ʳ Δ} (t : Term Θ Γ A) →
           [ σ ˢ∘ʳ ρ ]ˢ t ≈ [ σ ]ˢ ([ ρ ]ʳ t)
  [ˢ∘ʳ]ˢ (tm-var x) = ≈-refl
  [ˢ∘ʳ]ˢ (tm-meta M ts) = ≈-meta (λ i → [ˢ∘ʳ]ˢ (ts i))
  [ˢ∘ʳ]ˢ (tm-oper f es) = ≈-oper (λ i → [⇑ˢ∘ʳ] (es i))

  -- composition commutes with extension

  ⇑ˢ-∘ˢ : ∀ {Θ} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Δ ⇒ˢ Ξ} →
          ⇑ˢ {Ξ = Ψ} (τ ∘ˢ σ) ≈ˢ ⇑ˢ τ ∘ˢ ⇑ˢ σ
  ⇑ˢ-∘ˢ {σ = σ} {τ = τ} (var-inl x) =  ≈-trans (≈-sym ([ʳ∘ˢ]ˢ (σ x))) ([ˢ∘ʳ]ˢ (σ x))
  ⇑ˢ-∘ˢ (var-inr y) = ≈-refl

  -- substitition action is functorial

  [∘]ˢ : ∀ {Θ} {Γ Δ Ξ} {A} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Δ ⇒ˢ Ξ} (t : Term Θ Γ A) →
         [ τ ∘ˢ σ ]ˢ t ≈ [ τ ]ˢ ([ σ ]ˢ t)
  [∘]ˢ (tm-var x) = ≈-refl
  [∘]ˢ (tm-meta M ts) = ≈-meta (λ i → [∘]ˢ (ts i))
  [∘]ˢ (tm-oper f es) = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) ⇑ˢ-∘ˢ) ([∘]ˢ (es i)))

  -- Terms form a relative monad

  module _ {Θ : MetaContext} where
    open Categories.Category
    open Categories.Functor using (Functor)
    open Categories.Category.Instance.Setoids
    open Categories.Monad.Relative
    open Function.Equality using () renaming (setoid to Π-setoid)
    open import SecondOrder.IndexedCategory

    -- The embedding of contexts into setoids indexed by sorts

    slots : Functor Contexts (IndexedCategory sort (Setoids ℓ ℓ))
    slots = record
              { F₀ = λ Γ A → setoid (A ∈ Γ)
              ; F₁ = λ ρ A → record { _⟨$⟩_ = ρ ; cong = cong ρ }
              ; identity = λ A ξ → ξ
              ; homomorphism = λ {_} {_} {_} {ρ} {σ} A {_} {_} ξ → cong σ (cong ρ ξ)
              ; F-resp-≈ = λ ξ A ζ → trans (ξ _) (cong _ ζ)
              }


    -- The relative monad of terms over contexts

    Term-Monad : Monad slots
    Term-Monad =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record
        { F₀ = Term-setoid Θ
        ; unit = λ A → record { _⟨$⟩_ = tm-var ; cong = λ ξ → ≈-≡ (cong tm-var ξ) }
        ; extend = λ σ A → record { _⟨$⟩_ =  [ (σ _ ⟨$⟩_) ]ˢ_ ; cong = []ˢ-resp-≈ (σ _ ⟨$⟩_)}
        ; identityʳ = λ {_} {_} {σ} A {_} {_} ξ → func-cong (σ A) ξ
        ; identityˡ = λ A → ≈-trans [id]ˢ
        ; assoc = λ {_} {_} {_} {σ} {ρ} A {_} {t} ξ → ≈-trans ([]ˢ-resp-≈ _ ξ) ([∘]ˢ t)
        ; extend-≈ = λ {Γ} {Δ} {σ} {ρ} ζ B {s} {t} ξ → []ˢ-resp-≈ˢ-≈ (λ x → ζ _ refl) ξ
        }


    -- the category of contexts and substitutions

    Terms : Category ℓ ℓ ℓ
    Terms = SecondOrder.RelativeKleisli.Kleisli Term-Monad

    -- the binary coproduct structure on Terms

    infixl 7 [_,_]ˢ

    [_,_]ˢ : ∀ {Γ Δ Ξ} (σ : Θ ⊕ Γ ⇒ˢ Ξ) (τ : Θ ⊕ Δ ⇒ˢ Ξ) → Θ ⊕ (Γ ,, Δ) ⇒ˢ Ξ
    [ σ , τ ]ˢ (var-inl x) = σ x
    [ σ , τ ]ˢ (var-inr y) = τ y

    inlˢ : ∀ {Γ Δ} → Θ ⊕ Γ ⇒ˢ Γ ,, Δ
    inlˢ x = tm-var (var-inl x)

    inrˢ : ∀ {Γ Δ} → Θ ⊕ Δ ⇒ˢ Γ ,, Δ
    inrˢ y = tm-var (var-inr y)

    uniqueˢ : ∀ {Γ Δ Ξ} {τ : Θ ⊕ Γ ,, Δ ⇒ˢ Ξ} {ρ : Θ ⊕ Γ ⇒ˢ Ξ} {σ : Θ ⊕ Δ ⇒ˢ Ξ}
              → τ ∘ˢ inlˢ ≈ˢ ρ
              → τ ∘ˢ inrˢ ≈ˢ σ
              → [ ρ , σ ]ˢ ≈ˢ τ
    uniqueˢ ξ ζ (var-inl x) = ≈-sym (ξ x)
    uniqueˢ ξ ζ (var-inr y) = ≈-sym (ζ y)


    Terms-+ : Categories.Category.Cocartesian.BinaryCoproducts Terms
    Terms-+ =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record {
        coproduct =
          λ {Γ Δ} →
          record
            { A+B = Γ ,, Δ
            ; i₁ = λ A → record { _⟨$⟩_ = inlˢ ; cong = λ ξ → ≈-≡ (cong _ ξ) }
            ; i₂ = λ A → record { _⟨$⟩_ = inrˢ ; cong = λ ξ → ≈-≡ (cong _ ξ) }
            ; [_,_] = λ σ τ A → record { _⟨$⟩_ =  [ σ _ ⟨$⟩_ , τ _ ⟨$⟩_ ]ˢ ; cong = λ ξ → ≈-≡ (cong _ ξ) }
            ; inject₁ = λ A ξ → ≈-≡ (cong _ ξ)
            ; inject₂ = λ A ξ → ≈-≡ (cong _ ξ)
            ; unique = {!!}
            }
      }
