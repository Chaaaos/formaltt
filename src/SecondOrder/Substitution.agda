-- {-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; setoid; cong; trans)
import Function.Equality
open import Relation.Binary using (Setoid)

import Categories.Category
import Categories.Functor
import Categories.Category.Instance.Setoids
import Categories.Monad.Relative
import Categories.Category.Equivalence
import Categories.Category.Cocartesian
import Categories.Category.Cartesian
import Categories.Category.Construction.Functors


import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.VRenaming
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
  open SecondOrder.VRenaming Σ

  -- substitution

  infix 4 _⊕_⇒ˢ_

  _⊕_⇒ˢ_ : ∀ (Θ : MContext) (Γ Δ : VContext) → Set ℓ
  Θ ⊕ Γ ⇒ˢ Δ = ∀ {A} (x : A ∈ Γ) → Term Θ Δ A

  -- syntactic equality of substitutions

  infix 5 _≈ˢ_

  _≈ˢ_ : ∀ {Θ} {Γ Δ} (σ τ : Θ ⊕ Γ ⇒ˢ Δ) → Set ℓ
  _≈ˢ_ {Θ} {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≈ τ x

  -- equality of substitutions form a setoid
  ≈ˢ-refl : ∀ {Θ Γ Δ} {σ : Θ ⊕ Γ ⇒ˢ Δ}
          → σ ≈ˢ σ
  ≈ˢ-refl x = ≈-refl

  ≈ˢ-sym : ∀ {Θ Γ Δ} {σ τ : Θ ⊕ Γ ⇒ˢ Δ}
          → σ ≈ˢ τ
          → τ ≈ˢ σ
  ≈ˢ-sym eq x = ≈-sym (eq x)

  ≈ˢ-trans : ∀ {Θ Γ Δ} {σ τ μ : Θ ⊕ Γ ⇒ˢ Δ}
           → σ ≈ˢ τ → τ ≈ˢ μ
           → σ ≈ˢ μ
  ≈ˢ-trans eq1 eq2 x = ≈-trans (eq1 x) (eq2 x)

  substitution-setoid : ∀ (Γ Δ : VContext) (Θ : MContext) → Setoid ℓ ℓ
  substitution-setoid Γ Δ Θ =
    record
      { Carrier = Θ ⊕ Γ ⇒ˢ Δ
      ;  _≈_ = λ σ τ → σ ≈ˢ τ
      ; isEquivalence =
                      record
                        { refl = λ {σ} x → ≈ˢ-refl {σ = σ} x
                        ; sym = ≈ˢ-sym
                        ; trans = ≈ˢ-trans
                        }
      }

  congˢ : ∀ {Θ} {Γ Δ} {A} {σ τ : Θ ⊕ Γ ⇒ˢ Δ} {x : A ∈ Γ} → σ ≈ˢ τ → σ x ≈ τ x
  congˢ {x = x} eq = eq x

  congˢ-var :  ∀ {Θ} {Γ Δ} {A} {σ : Θ ⊕ Γ ⇒ˢ Δ} {x y : A ∈ Γ} → x ≡ y → σ x ≈ σ y
  congˢ-var refl = ≈-refl

  -- extension of a substitution

  ⇑ˢ : ∀ {Θ Γ Δ Ξ} → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ (Γ ,, Ξ) ⇒ˢ (Δ ,, Ξ)
  ⇑ˢ σ (var-inl x) = [ var-inl ]ᵛʳ σ x
  ⇑ˢ σ (var-inr y) = tm-var (var-inr y)

  -- extension respects equality of substitutions

  ⇑ˢ-resp-≈ˢ : ∀ {Θ Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒ˢ Δ} → σ ≈ˢ τ → ⇑ˢ {Ξ = Ξ} σ ≈ˢ ⇑ˢ {Ξ = Ξ} τ
  ⇑ˢ-resp-≈ˢ ξ (var-inl x) = []ᵛʳ-resp-≈ (ξ x)
  ⇑ˢ-resp-≈ˢ ξ (var-inr y) = ≈-refl

  -- the action of a renaming on a substitution

  infixr 6 _ᵛʳ∘ˢ_

  _ᵛʳ∘ˢ_ : ∀ {Θ} {Γ Δ Ξ} (ρ : Δ ⇒ᵛʳ Ξ) (σ : Θ ⊕ Γ ⇒ˢ Δ) → Θ ⊕ Γ ⇒ˢ Ξ
  (ρ ᵛʳ∘ˢ σ) x =  [ ρ ]ᵛʳ (σ x)

  infixl 6 _ˢ∘ᵛʳ_

  _ˢ∘ᵛʳ_ : ∀ {Θ} {Γ Δ Ξ} (σ : Θ ⊕ Δ ⇒ˢ Ξ) (ρ : Γ ⇒ᵛʳ Δ)  → Θ ⊕ Γ ⇒ˢ Ξ
  (σ ˢ∘ᵛʳ ρ) x =  σ (ρ x)

  -- extension commutes with renaming action

  ⇑ˢ-ˢ∘ᵛʳ : ∀ {Θ} {Γ Δ Ξ Ψ} {ρ : Γ ⇒ᵛʳ Δ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} → ⇑ˢ {Ξ = Ψ} (σ ˢ∘ᵛʳ ρ) ≈ˢ ⇑ˢ σ ˢ∘ᵛʳ ⇑ᵛʳ ρ
  ⇑ˢ-ˢ∘ᵛʳ (var-inl x) = ≈-refl
  ⇑ˢ-ˢ∘ᵛʳ (var-inr x) = ≈-refl

  -- the action of a substitution on a term

  infix 6 [_]ˢ_

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

  -- the identity substitution preserves equality of terms
  [id]ˢ-resp-≈ : ∀ {Θ} {Γ} {A} {t s : Term Θ Γ A} → t ≈ s → [ idˢ ]ˢ t ≈ s
  [id]ˢ-resp-≈ t≈s = ≈-trans ([]ˢ-resp-≈ idˢ t≈s) [id]ˢ


  -- if a substiution is equal to the identity then it acts trivially
  ≈ˢ-idˢ-[]ˢ : ∀ {Θ} {Γ} {A} {σ : Θ ⊕ Γ ⇒ˢ Γ} {t : Term Θ Γ A} → σ ≈ˢ idˢ → [ σ ]ˢ t ≈ t
  ≈ˢ-idˢ-[]ˢ {t = t} ξ = ≈-trans ([]ˢ-resp-≈ˢ t ξ) [id]ˢ

  -- interaction of extension and right renaming action

  [⇑ˢ∘ᵛʳ] : ∀ {Θ} {A} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} {ρ : Γ ⇒ᵛʳ Δ} (t : Term Θ (Γ ,, Ψ) A) →
         [ ⇑ˢ (σ ˢ∘ᵛʳ ρ) ]ˢ t ≈ [ ⇑ˢ σ ]ˢ [ ⇑ᵛʳ ρ ]ᵛʳ t
  [⇑ˢ∘ᵛʳ] (tm-var (var-inl x)) = ≈-refl
  [⇑ˢ∘ᵛʳ] (tm-var (var-inr x)) = ≈-refl
  [⇑ˢ∘ᵛʳ] (tm-meta M ts) = ≈-meta (λ i → [⇑ˢ∘ᵛʳ] (ts i))
  [⇑ˢ∘ᵛʳ] (tm-oper f es) = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) (⇑ˢ-resp-≈ˢ ⇑ˢ-ˢ∘ᵛʳ)) ([⇑ˢ∘ᵛʳ] (es i)))

  -- interaction of extension and left renaming action

  ⇑ˢ-ᵛʳ∘ˢ : ∀ {Θ} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {ρ : Δ ⇒ᵛʳ Ξ} →
           ⇑ˢ {Ξ = Ψ} (ρ ᵛʳ∘ˢ σ) ≈ˢ ⇑ᵛʳ ρ ᵛʳ∘ˢ ⇑ˢ σ
  ⇑ˢ-ᵛʳ∘ˢ (var-inl x) = ≈-trans (≈-sym [∘]ᵛʳ) (≈-trans ([]ᵛʳ-resp-≡ᵛʳ (λ _ → refl)) [∘]ᵛʳ)
  ⇑ˢ-ᵛʳ∘ˢ (var-inr y) = ≈-refl

  [⇑ᵛʳ∘ˢ] : ∀ {Θ} {A} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {ρ : Δ ⇒ᵛʳ Ξ} (t : Term Θ (Γ ,, Ψ) A) →
         [ ⇑ˢ (ρ ᵛʳ∘ˢ σ) ]ˢ t ≈ [ ⇑ᵛʳ ρ ]ᵛʳ ([ ⇑ˢ σ ]ˢ t)
  [⇑ᵛʳ∘ˢ] (tm-var x) = ⇑ˢ-ᵛʳ∘ˢ x
  [⇑ᵛʳ∘ˢ] (tm-meta M ts) = ≈-meta (λ i → [⇑ᵛʳ∘ˢ] (ts i))
  [⇑ᵛʳ∘ˢ] (tm-oper f es) = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) (⇑ˢ-resp-≈ˢ ⇑ˢ-ᵛʳ∘ˢ)) ([⇑ᵛʳ∘ˢ] (es i)))

  -- functoriality of left renaming action

  [ᵛʳ∘ˢ]ˢ : ∀ {Θ} {A} {Γ Δ Ξ} {ρ : Δ ⇒ᵛʳ Ξ} {σ : Θ ⊕ Γ ⇒ˢ Δ} (t : Term Θ Γ A) →
           [ ρ ᵛʳ∘ˢ σ ]ˢ t ≈ [ ρ ]ᵛʳ [ σ ]ˢ t
  [ᵛʳ∘ˢ]ˢ (tm-var x) = ≈-refl
  [ᵛʳ∘ˢ]ˢ (tm-meta M ts) = ≈-meta (λ i → [ᵛʳ∘ˢ]ˢ (ts i))
  [ᵛʳ∘ˢ]ˢ (tm-oper f es) = ≈-oper (λ i → [⇑ᵛʳ∘ˢ] (es i))

  -- functoriality of right renaming action

  [ˢ∘ᵛʳ]ˢ : ∀ {Θ} {A} {Γ Δ Ξ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} {ρ : Γ ⇒ᵛʳ Δ} (t : Term Θ Γ A) →
           [ σ ˢ∘ᵛʳ ρ ]ˢ t ≈ [ σ ]ˢ [ ρ ]ᵛʳ t
  [ˢ∘ᵛʳ]ˢ (tm-var x) = ≈-refl
  [ˢ∘ᵛʳ]ˢ (tm-meta M ts) = ≈-meta (λ i → [ˢ∘ᵛʳ]ˢ (ts i))
  [ˢ∘ᵛʳ]ˢ (tm-oper f es) = ≈-oper (λ i → [⇑ˢ∘ᵛʳ] (es i))

  -- composition commutes with extension

  ⇑ˢ-∘ˢ : ∀ {Θ} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Δ ⇒ˢ Ξ} →
          ⇑ˢ {Ξ = Ψ} (τ ∘ˢ σ) ≈ˢ ⇑ˢ τ ∘ˢ ⇑ˢ σ
  ⇑ˢ-∘ˢ {σ = σ} {τ = τ} (var-inl x) =  ≈-trans (≈-sym ([ᵛʳ∘ˢ]ˢ (σ x))) ([ˢ∘ᵛʳ]ˢ (σ x))
  ⇑ˢ-∘ˢ (var-inr y) = ≈-refl

  -- substitition action is functorial

  [∘]ˢ : ∀ {Θ} {Γ Δ Ξ} {A} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Δ ⇒ˢ Ξ} (t : Term Θ Γ A) →
         [ τ ∘ˢ σ ]ˢ t ≈ [ τ ]ˢ ([ σ ]ˢ t)
  [∘]ˢ (tm-var x) = ≈-refl
  [∘]ˢ (tm-meta M ts) = ≈-meta (λ i → [∘]ˢ (ts i))
  [∘]ˢ (tm-oper f es) = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) ⇑ˢ-∘ˢ) ([∘]ˢ (es i)))

  -- Terms form a relative monad

  module _ where
    open Categories.Category
    open Categories.Functor using (Functor)
    open Categories.Category.Construction.Functors
    open Categories.Category.Cartesian.BinaryProducts
    open Categories.Category.Instance.Setoids
    open Categories.Monad.Relative
    open Function.Equality using () renaming (setoid to Π-setoid)
    open Categories.Category.Equivalence using (StrongEquivalence)
    open import SecondOrder.IndexedCategory
    open import SecondOrder.RelativeKleisli


    VCat : ∀ (Θ : MContext) (Δ : VContext) (A : sort) → Category ℓ ℓ ℓ
    VCat = λ Θ Δ A → record
                        { Obj = A ∈ Δ
                        ; _⇒_ = λ x y → {!!}
                        ; _≈_ = {!!}
                        ; id = {!!}
                        ; _∘_ = {!!}
                        ; assoc = {!!}
                        ; sym-assoc = {!!}
                        ; identityˡ = {!!}
                        ; identityʳ = {!!}
                        ; identity² = {!!}
                        ; equiv = {!!}
                        ; ∘-resp-≈ = {!!}
                        }

    Vslots : Functor (VContexts) (IndexedCategory sort (Setoids ℓ ℓ))
    Vslots = record
              { F₀ = {!!}
              ; F₁ = {!!}
              ; identity = λ A ξ → ξ
              ; homomorphism = λ {_} {_} {_} {ρ} {σ} A {_} {_} ξ → cong σ (cong ρ ξ)
              ; F-resp-≈ = λ ξ A ζ → trans (ξ _) (cong _ ζ)
              }

     -- The embedding of extended contexts into setoids indexed by sorts

    ⇑ᵗ-Vslots : ∀ (Γ : VContext) → Functor VContexts (IndexedCategory sort (Setoids ℓ ℓ))
    ⇑ᵗ-Vslots Γ = record
              { F₀ = λ Δ A → setoid (A ∈ (Δ ,, Γ))
              ; F₁ = λ ρ A → record { _⟨$⟩_ = ⇑ʳ ρ ; cong = cong (⇑ʳ ρ) } -- λ ρ A → record { _⟨$⟩_ = ρ ; cong = cong ρ }
              ; identity = λ A ξ → {!!} -- λ A ξ → ξ
              ; homomorphism = {!!} -- λ {_} {_} {_} {ρ} {σ} A {_} {_} ξ → cong σ (cong ρ ξ)
              ; F-resp-≈ = {!!} -- λ ξ A ζ → trans (ξ _) (cong _ ζ)
              }

  module _ {Θ : MContext} where
    open Categories.Category
    open Categories.Functor using (Functor)
    open Categories.Category.Instance.Setoids
    open Categories.Monad.Relative
    open Function.Equality using () renaming (setoid to Π-setoid)
    open Categories.Category.Equivalence using (StrongEquivalence)
    open import SecondOrder.IndexedCategory
    open import SecondOrder.RelativeKleisli


    -- The relative monad of terms over contexts

    Term-Monad : Monad Vslots
    Term-Monad =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record
        { F₀ = Term-setoid Θ
        ; unit = λ A → record { _⟨$⟩_ = idˢ ; cong = λ ξ → ≈-≡ (cong idˢ ξ) }
        ; extend = λ σ A → record { _⟨$⟩_ =  [ (σ _ ⟨$⟩_) ]ˢ_ ; cong = []ˢ-resp-≈ (σ _ ⟨$⟩_)}
        ; identityʳ = λ {_} {_} {σ} A {_} {_} ξ → func-cong (σ A) ξ
        ; identityˡ = λ A → ≈-trans [id]ˢ
        ; assoc = λ {_} {_} {_} {σ} {ρ} A {_} {t} ξ → ≈-trans ([]ˢ-resp-≈ _ ξ) ([∘]ˢ t)
        ; extend-≈ = λ {Γ} {Δ} {σ} {ρ} ζ B {s} {t} ξ → []ˢ-resp-≈ˢ-≈ (λ x → ζ _ refl) ξ
        }


    -- The relative monad of terms over extended contexts

    ⇑ᵗ-Term-Monad : ∀ (Γ : VContext) → Monad (⇑ᵗ-Vslots Γ)
    ⇑ᵗ-Term-Monad Γ =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record
        { F₀ = λ Δ A → Term-setoid Θ (Γ ,, Δ) A -- Term-setoid Θ
        ; unit = {!!} -- λ A → record { _⟨$⟩_ = idˢ ; cong = λ ξ → ≈-≡ (cong idˢ ξ) }
        ; extend = {!!} -- λ σ A → record { _⟨$⟩_ =  [ (σ _ ⟨$⟩_) ]ˢ_ ; cong = []ˢ-resp-≈ (σ _ ⟨$⟩_)}
        ; identityʳ = {!!} -- λ {_} {_} {σ} A {_} {_} ξ → func-cong (σ A) ξ
        ; identityˡ = {!!} -- λ A → ≈-trans [id]ˢ
        ; assoc = {!!} -- λ {_} {_} {_} {σ} {ρ} A {_} {t} ξ → ≈-trans ([]ˢ-resp-≈ _ ξ) ([∘]ˢ t)
        ; extend-≈ = {!!} -- λ {Γ} {Δ} {σ} {ρ} ζ B {s} {t} ξ → []ˢ-resp-≈ˢ-≈ (λ x → ζ _ refl) ξ
        }

    -- the category of contexts and substitutions

    -- we show below that the category of contexts and substitiions is equivalent
    -- to the Kleisli category for the Term relative monad. However, we define
    -- the category of contexts and substitutions directly, as that it is easier
    -- to work with it

    Terms : Category ℓ ℓ ℓ
    Terms =
      record
        { Obj = VContext
        ; _⇒_ = Θ ⊕_⇒ˢ_
        ; _≈_ =  _≈ˢ_
        ; id = idˢ
        ; _∘_ = _∘ˢ_
        ; assoc = λ {Γ} {Δ} {Ξ} {Ψ} {σ} {τ} {ψ} {A} x → [∘]ˢ (σ x)
        ; sym-assoc = λ {Γ} {Δ} {Ξ} {Ψ} {σ} {τ} {ψ} {A} x → ≈-sym ([∘]ˢ (σ x))
        ; identityˡ = λ x → [id]ˢ
        ; identityʳ = λ x → ≈-refl
        ; identity² = λ x → ≈-refl
        ; equiv = record { refl = λ {σ} {A} → ≈ˢ-refl {σ = σ} ; sym = ≈ˢ-sym ; trans = ≈ˢ-trans }
        ; ∘-resp-≈ = λ f≈ˢg g≈ˢi x → []ˢ-resp-≈ˢ-≈ f≈ˢg (g≈ˢi x)
        }

    Terms-is-Kleisli : StrongEquivalence Terms (Kleisli Term-Monad)
    Terms-is-Kleisli =
      record
      { F = record
              { F₀ = λ Γ → Γ
              ; F₁ = λ σ A → record { _⟨$⟩_ = λ x → σ x ; cong = λ i≡j → ≈-≡ (cong σ i≡j) }
              ; identity = λ A eq → ≈-≡ (cong idˢ eq)
              ; homomorphism = λ {Γ} {Δ} {Ξ} {σ} {τ} A eq → ≈-≡ (cong (λ x → [ τ ]ˢ σ x) eq)
              ; F-resp-≈ = λ {Γ} {Δ} {σ} {τ} hom_eq A eq
                         → ≈-trans (congˢ hom_eq) (≈-≡ (cong τ eq))
              }
      ; G =
          let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
          record
              { F₀ = λ Γ → Γ
              ; F₁ = λ {Γ} {Δ} σ {A} → λ x → σ A ⟨$⟩ x
              ; identity = λ x → ≈-refl
              ; homomorphism = λ x → ≈-refl
              ; F-resp-≈ = λ {Γ} {Δ} {σ} {τ} σ≈τ {A} x → σ≈τ A refl
              }
      ; weak-inverse =
          let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
          record
          { F∘G≈id =
                   record
                   { F⇒G =
                         record
                         { η = λ Γ A → record { _⟨$⟩_ = idˢ
                                               ; cong = λ i≡j → ≈-≡ (cong idˢ i≡j)
                                               }
                         ; commute = λ σ A x≡y → [id]ˢ-resp-≈ (≈-≡ (cong (λ x → σ A ⟨$⟩ x) x≡y))
                         ; sym-commute = λ σ A x≡y
                                       → ≈-sym ([id]ˢ-resp-≈ (≈-≡ (cong (λ x → σ A ⟨$⟩ x ) (sym x≡y))))
                         }
                   ; F⇐G =
                         record
                         { η = λ Γ A → record { _⟨$⟩_ = idˢ
                                               ; cong = λ i≡j → ≈-≡ (cong idˢ i≡j)
                                               }
                         ; commute = λ σ A x≡y → [id]ˢ-resp-≈ (≈-≡ (cong (λ x → σ A ⟨$⟩ x) x≡y))
                         ; sym-commute = λ σ A x≡y
                                       → ≈-sym ([id]ˢ-resp-≈ (≈-≡ (cong (λ x → σ A ⟨$⟩ x ) (sym x≡y))))
                         }
                   ; iso = λ Γ → record { isoˡ = λ A x≡y → ≈-≡ (cong tm-var x≡y)
                                         ; isoʳ = λ A x≡y → ≈-≡ (cong tm-var x≡y)
                                         }
                   }
          ; G∘F≈id =
                   record
                   { F⇒G =
                         record
                         { η = λ Γ x → tm-var x
                         ; commute = λ σ x → [id]ˢ
                         ; sym-commute = λ σ x → ≈-sym [id]ˢ
                         }
                   ; F⇐G =
                         record
                         { η = λ Γ x → tm-var x
                         ; commute = λ σ x → [id]ˢ
                         ; sym-commute = λ σ x → ≈-sym [id]ˢ
                         }
                   ; iso = λ Γ → record { isoˡ = λ x → ≈-refl
                                         ; isoʳ = λ x → ≈-refl
                                         }
                   }
          }
      }

    -- the binary coproduct structure on Terms

    infixl 7 [_,_]ˢ

    [_,_]ˢ : ∀ {Γ Δ Ξ} (σ : Θ ⊕ Γ ⇒ˢ Ξ) (τ : Θ ⊕ Δ ⇒ˢ Ξ) → Θ ⊕ (Γ ,, Δ) ⇒ˢ Ξ
    [ σ , τ ]ˢ (var-inl x) = σ x
    [ σ , τ ]ˢ (var-inr y) = τ y

    inlˢ : ∀ {Γ Δ} → Θ ⊕ Γ ⇒ˢ Γ ,, Δ
    inlˢ x = tm-var (var-inl x)

    inrˢ : ∀ {Γ Δ} → Θ ⊕ Δ ⇒ˢ Γ ,, Δ
    inrˢ y = tm-var (var-inr y)

    [,]ˢ-resp-≈ˢ : ∀ {Γ Δ Ξ} {σ₁ σ₂ : Θ ⊕ Γ ⇒ˢ Ξ} {τ₁ τ₂ : Θ ⊕ Δ ⇒ˢ Ξ} →
                   σ₁ ≈ˢ σ₂ → τ₁ ≈ˢ τ₂ → [ σ₁ , τ₁ ]ˢ ≈ˢ [ σ₂ , τ₂ ]ˢ
    [,]ˢ-resp-≈ˢ ζ ξ (var-inl x) = ζ x
    [,]ˢ-resp-≈ˢ ζ ξ (var-inr y) = ξ y

    uniqueˢ : ∀ {Γ Δ Ξ} {τ : Θ ⊕ Γ ,, Δ ⇒ˢ Ξ} {ρ : Θ ⊕ Γ ⇒ˢ Ξ} {σ : Θ ⊕ Δ ⇒ˢ Ξ}
              → τ ∘ˢ inlˢ ≈ˢ ρ
              → τ ∘ˢ inrˢ ≈ˢ σ
              → [ ρ , σ ]ˢ ≈ˢ τ
    uniqueˢ ξ ζ (var-inl x) = ≈-sym (ξ x)
    uniqueˢ ξ ζ (var-inr y) = ≈-sym (ζ y)

    Terms-Coproduct : Categories.Category.Cocartesian.BinaryCoproducts Terms
    Terms-Coproduct =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record {
        coproduct =
          λ {Γ Δ} →
          record
            { A+B = Γ ,, Δ
            ; i₁ = inlˢ
            ; i₂ = inrˢ
            ; [_,_] = [_,_]ˢ
            ; inject₁ = λ x → ≈-≡ refl
            ; inject₂ = λ x → ≈-≡ refl
            ; unique = λ {Ξ} {h} p₁ p₂ → uniqueˢ {τ = h} p₁ p₂
            }
      }

    open Categories.Category.Cocartesian.BinaryCoproducts Terms-Coproduct

    -- the sum of subsitutions

    infixl 6 _+ˢ_

    _+ˢ_ : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} (σ : Θ ⊕ Γ₁ ⇒ˢ Δ₁) (τ : Θ ⊕ Γ₂ ⇒ˢ Δ₂) → Θ ⊕ Γ₁ ,, Γ₂ ⇒ˢ Δ₁ ,, Δ₂
    σ +ˢ τ = σ +₁ τ

    -- reassociations of context sums

    assoc-l : ∀ {Γ Δ Ξ} → Θ ⊕ (Γ ,, Δ) ,, Ξ ⇒ˢ Γ ,, (Δ ,, Ξ)
    assoc-l (var-inl (var-inl x)) = tm-var (var-inl x)
    assoc-l (var-inl (var-inr y)) = tm-var (var-inr (var-inl y))
    assoc-l (var-inr z) = tm-var (var-inr (var-inr z))

    assoc-r : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ,, (Δ ,, Ξ) ⇒ˢ (Γ ,, Δ) ,, Ξ
    assoc-r (var-inl x) = tm-var (var-inl (var-inl x))
    assoc-r (var-inr (var-inl y)) = tm-var (var-inl (var-inr y))
    assoc-r (var-inr (var-inr z)) = tm-var (var-inr z)

    assoc-lr : ∀ {Γ Δ Ξ} → assoc-l {Γ = Γ} {Δ = Δ} {Ξ = Ξ} ∘ˢ assoc-r {Γ = Γ} {Δ = Δ} {Ξ = Ξ} ≈ˢ idˢ
    assoc-lr (var-inl x) = ≈-refl
    assoc-lr (var-inr (var-inl y)) = ≈-refl
    assoc-lr (var-inr (var-inr y)) = ≈-refl

    assoc-rl : ∀ {Γ Δ Ξ} → assoc-r {Γ = Γ} {Δ = Δ} {Ξ = Ξ} ∘ˢ assoc-l {Γ = Γ} {Δ = Δ} {Ξ = Ξ} ≈ˢ idˢ
    assoc-rl (var-inl (var-inl x)) = ≈-refl
    assoc-rl (var-inl (var-inr x)) = ≈-refl
    assoc-rl (var-inr z) = ≈-refl

    -- summing with the empty context is the unit

    sum-ctx-empty-r : ∀ {Γ} → Θ ⊕ Γ ,, ctx-empty ⇒ˢ Γ
    sum-ctx-empty-r (var-inl x) = tm-var x

    sum-ctx-empty-l : ∀ {Γ} → Θ ⊕ ctx-empty ,, Γ ⇒ˢ Γ
    sum-ctx-empty-l (var-inr x) = tm-var x
