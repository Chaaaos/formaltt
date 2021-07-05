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

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.VRenaming
import SecondOrder.MRenaming
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
  open SecondOrder.MRenaming Σ
  open SecondOrder.VRenaming Σ

  -- substitution

  infix 4 _⊕_⇒ˢ_

  _⊕_⇒ˢ_ : ∀ (Θ : MContext) (Γ Δ : VContext) → Set ℓ
  Θ ⊕ Γ ⇒ˢ Δ = ∀ {A} (x : A ∈ Γ) → Term Θ Δ A

  -- substitution preserves propositionnal equality

  σ-resp-≡ : ∀ {Θ Γ Δ A} {x y : A ∈ Γ} {σ : Θ ⊕ Γ ⇒ˢ Δ} → x ≡ y → σ x ≡ σ y
  σ-resp-≡ refl = refl

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
  ⇑ˢ σ (var-inl x) = [ var-inl ]ᵛ σ x
  ⇑ˢ σ (var-inr y) = tm-var (var-inr y)

  -- extension respects equality of substitutions

  ⇑ˢ-resp-≈ˢ : ∀ {Θ Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒ˢ Δ} → σ ≈ˢ τ → ⇑ˢ {Ξ = Ξ} σ ≈ˢ ⇑ˢ {Ξ = Ξ} τ
  ⇑ˢ-resp-≈ˢ ξ (var-inl x) = []ᵛ-resp-≈ (ξ x)
  ⇑ˢ-resp-≈ˢ ξ (var-inr y) = ≈-refl

  -- the compositions of renamings and substitutions

  infixr 6 _ᵛ∘ˢ_

  _ᵛ∘ˢ_ : ∀ {Θ} {Γ Δ Ξ} (ρ : Δ ⇒ᵛ Ξ) (σ : Θ ⊕ Γ ⇒ˢ Δ) → Θ ⊕ Γ ⇒ˢ Ξ
  (ρ ᵛ∘ˢ σ) x =  [ ρ ]ᵛ (σ x)

  infixl 6 _ˢ∘ᵛ_

  _ˢ∘ᵛ_ : ∀ {Θ} {Γ Δ Ξ} (σ : Θ ⊕ Δ ⇒ˢ Ξ) (ρ : Γ ⇒ᵛ Δ)  → Θ ⊕ Γ ⇒ˢ Ξ
  (σ ˢ∘ᵛ ρ) x =  σ (ρ x)

  -- the composition of metarenamings and substitutions

  infixr 6 _ᵐ∘ˢ_

  _ᵐ∘ˢ_ : ∀ {Θ Ω} {Γ Δ} (μ : Θ ⇒ᵐ Ω) (σ : Θ ⊕ Γ ⇒ˢ Δ) → Ω ⊕ Γ ⇒ˢ Δ
  (μ ᵐ∘ˢ σ) x =  [ μ ]ᵐ σ x

  -- infixl 6 _ˢ∘ᵐ_

  -- _ˢ∘ᵐ_ : ∀ {Ω Θ} {Γ Δ} (σ : Ω ⊕ Γ ⇒ˢ Δ) (μ : Θ ⇒ᵐ Ω)  → Ω ⊕ Γ ⇒ˢ Δ
  -- (σ ˢ∘ᵐ μ) x =  {![_]ˢ_!}


  -- extension commutes with renaming action

  ⇑ˢ-resp-ˢ∘ᵛ : ∀ {Θ} {Γ Δ Ξ Ψ} {ρ : Γ ⇒ᵛ Δ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} → ⇑ˢ {Ξ = Ψ} (σ ˢ∘ᵛ ρ) ≈ˢ ⇑ˢ σ ˢ∘ᵛ ⇑ᵛ ρ
  ⇑ˢ-resp-ˢ∘ᵛ (var-inl x) = ≈-refl
  ⇑ˢ-resp-ˢ∘ᵛ (var-inr x) = ≈-refl

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

  ⇑ˢ-resp-idˢ : ∀ {Θ} {Γ Δ} → ⇑ˢ idˢ ≈ˢ idˢ {Θ = Θ} {Γ = Γ ,, Δ}
  ⇑ˢ-resp-idˢ (var-inl x) = ≈-refl
  ⇑ˢ-resp-idˢ (var-inr y) = ≈-refl

  -- the identity substution acts trivially

  [idˢ] : ∀ {Θ} {Γ} {A} {t : Term Θ Γ A} → [ idˢ ]ˢ t ≈ t
  [idˢ] {t = tm-var x} = ≈-refl
  [idˢ] {t = tm-meta M ts} = ≈-meta (λ i → [idˢ])
  [idˢ] {t = tm-oper f es} = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) ⇑ˢ-resp-idˢ) [idˢ])

  -- the identity substitution preserves equality of terms
  [idˢ]-resp-≈ : ∀ {Θ} {Γ} {A} {t s : Term Θ Γ A} → t ≈ s → [ idˢ ]ˢ t ≈ s
  [idˢ]-resp-≈ t≈s = ≈-trans ([]ˢ-resp-≈ idˢ t≈s) [idˢ]


  -- if a substiution is equal to the identity then it acts trivially
  ≈ˢ-idˢ-[]ˢ : ∀ {Θ} {Γ} {A} {σ : Θ ⊕ Γ ⇒ˢ Γ} {t : Term Θ Γ A} → σ ≈ˢ idˢ → [ σ ]ˢ t ≈ t
  ≈ˢ-idˢ-[]ˢ {t = t} ξ = ≈-trans ([]ˢ-resp-≈ˢ t ξ) [idˢ]

  -- interaction of extension and right renaming action

  [⇑ˢ∘ᵛ] : ∀ {Θ} {A} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} {ρ : Γ ⇒ᵛ Δ} (t : Term Θ (Γ ,, Ψ) A) →
         [ ⇑ˢ (σ ˢ∘ᵛ ρ) ]ˢ t ≈ [ ⇑ˢ σ ]ˢ [ ⇑ᵛ ρ ]ᵛ t
  [⇑ˢ∘ᵛ] (tm-var (var-inl x)) = ≈-refl
  [⇑ˢ∘ᵛ] (tm-var (var-inr x)) = ≈-refl
  [⇑ˢ∘ᵛ] (tm-meta M ts) = ≈-meta (λ i → [⇑ˢ∘ᵛ] (ts i))
  [⇑ˢ∘ᵛ] (tm-oper f es) = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) (⇑ˢ-resp-≈ˢ ⇑ˢ-resp-ˢ∘ᵛ)) ([⇑ˢ∘ᵛ] (es i)))

  -- interaction of extension and left renaming action

  ⇑ˢ-resp-ᵛ∘ˢ : ∀ {Θ} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {ρ : Δ ⇒ᵛ Ξ} →
           ⇑ˢ {Ξ = Ψ} (ρ ᵛ∘ˢ σ) ≈ˢ ⇑ᵛ ρ ᵛ∘ˢ ⇑ˢ σ
  ⇑ˢ-resp-ᵛ∘ˢ (var-inl x) = ≈-trans (≈-sym [∘ᵛ]) (≈-trans ([]ᵛ-resp-≡ᵛ (λ _ → refl)) [∘ᵛ])
  ⇑ˢ-resp-ᵛ∘ˢ (var-inr y) = ≈-refl

  [⇑ᵛ∘ˢ] : ∀ {Θ} {A} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {ρ : Δ ⇒ᵛ Ξ} (t : Term Θ (Γ ,, Ψ) A) →
         [ ⇑ˢ (ρ ᵛ∘ˢ σ) ]ˢ t ≈ [ ⇑ᵛ ρ ]ᵛ ([ ⇑ˢ σ ]ˢ t)
  [⇑ᵛ∘ˢ] (tm-var x) = ⇑ˢ-resp-ᵛ∘ˢ x
  [⇑ᵛ∘ˢ] (tm-meta M ts) = ≈-meta (λ i → [⇑ᵛ∘ˢ] (ts i))
  [⇑ᵛ∘ˢ] (tm-oper f es) = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) (⇑ˢ-resp-≈ˢ ⇑ˢ-resp-ᵛ∘ˢ)) ([⇑ᵛ∘ˢ] (es i)))

  -- action of the composition of a renaming and a substitution

  [ᵛ∘ˢ] : ∀ {Θ} {A} {Γ Δ Ξ} {ρ : Δ ⇒ᵛ Ξ} {σ : Θ ⊕ Γ ⇒ˢ Δ} (t : Term Θ Γ A) →
           [ ρ ᵛ∘ˢ σ ]ˢ t ≈ [ ρ ]ᵛ [ σ ]ˢ t
  [ᵛ∘ˢ] (tm-var x) = ≈-refl
  [ᵛ∘ˢ] (tm-meta M ts) = ≈-meta (λ i → [ᵛ∘ˢ] (ts i))
  [ᵛ∘ˢ] (tm-oper f es) = ≈-oper (λ i → [⇑ᵛ∘ˢ] (es i))

  -- action of the composition of a substitution and a renaming

  [ˢ∘ᵛ] : ∀ {Θ} {A} {Γ Δ Ξ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} {ρ : Γ ⇒ᵛ Δ} (t : Term Θ Γ A) →
           [ σ ˢ∘ᵛ ρ ]ˢ t ≈ [ σ ]ˢ [ ρ ]ᵛ t
  [ˢ∘ᵛ] (tm-var x) = ≈-refl
  [ˢ∘ᵛ] (tm-meta M ts) = ≈-meta (λ i → [ˢ∘ᵛ] (ts i))
  [ˢ∘ᵛ] (tm-oper f es) = ≈-oper (λ i → [⇑ˢ∘ᵛ] (es i))


  -- the action of renamings and metarenamings don't interfere with each other

  []ᵛ-[]ᵐ : ∀ {Θ Ω Γ Δ A} (ρ : Γ ⇒ᵛ Δ) (μ : Θ ⇒ᵐ Ω) (t : Term Θ Γ A) → [ ρ ]ᵛ ([ μ ]ᵐ t) ≈ [ μ ]ᵐ ([ ρ ]ᵛ t)
  []ᵛ-[]ᵐ ρ μ (tm-var x) = ≈-refl
  []ᵛ-[]ᵐ ρ μ (tm-meta M ts) = ≈-meta (λ i → []ᵛ-[]ᵐ ρ μ (ts i))
  []ᵛ-[]ᵐ ρ μ (tm-oper f es) = ≈-oper (λ i → []ᵛ-[]ᵐ  [ (λ x → var-inl (ρ x)) , (λ x → var-inr x) ]ᵛ  μ (es i))

  -- substitution extension interacts nicely with the composition of a renaming and a substitution

  ⇑ˢ-ᵐ∘ˢ : ∀ {Θ Ω Γ Δ Ξ} (μ : Θ ⇒ᵐ Ω) (σ : Θ ⊕ Γ ⇒ˢ Δ) →  ⇑ˢ {Ξ = Ξ} (μ ᵐ∘ˢ σ) ≈ˢ μ ᵐ∘ˢ ⇑ˢ σ
  ⇑ˢ-ᵐ∘ˢ μ σ (var-inl x) = []ᵛ-[]ᵐ var-inl μ (σ x)
  ⇑ˢ-ᵐ∘ˢ μ σ (var-inr x) = ≈-refl

  -- action of the composition of a metarenaming and a substitution

  [ᵐ∘ˢ] : ∀ {Θ Ω} {A} {Γ Δ} {μ : Θ ⇒ᵐ Ω} {σ : Θ ⊕ Γ ⇒ˢ Δ} (t : Term Θ Γ A) →
           [ μ ᵐ∘ˢ σ ]ˢ ( [ μ ]ᵐ t) ≈ [ μ ]ᵐ [ σ ]ˢ t
  [ᵐ∘ˢ] (tm-var x) = ≈-refl
  [ᵐ∘ˢ] {μ = μ} {σ = σ} (tm-meta M ts) = ≈-meta λ i → ([ᵐ∘ˢ] (ts i))
  [ᵐ∘ˢ] {μ = μ} {σ = σ} (tm-oper f es) = ≈-oper λ i →
                                  ≈-trans
                                    ([]ˢ-resp-≈ˢ ([ μ ]ᵐ (es i)) (⇑ˢ-ᵐ∘ˢ μ σ))
                                    ([ᵐ∘ˢ] (es i))


  -- composition commutes with extension

  ⇑ˢ-resp-∘ˢ : ∀ {Θ} {Γ Δ Ξ Ψ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Δ ⇒ˢ Ξ} →
          ⇑ˢ {Ξ = Ψ} (τ ∘ˢ σ) ≈ˢ ⇑ˢ τ ∘ˢ ⇑ˢ σ
  ⇑ˢ-resp-∘ˢ {σ = σ} {τ = τ} (var-inl x) =  ≈-trans (≈-sym ([ᵛ∘ˢ] (σ x))) ([ˢ∘ᵛ] (σ x))
  ⇑ˢ-resp-∘ˢ (var-inr y) = ≈-refl

  -- substitition action is functorial

  [∘ˢ] : ∀ {Θ} {Γ Δ Ξ} {A} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Δ ⇒ˢ Ξ} (t : Term Θ Γ A) →
         [ τ ∘ˢ σ ]ˢ t ≈ [ τ ]ˢ ([ σ ]ˢ t)
  [∘ˢ] (tm-var x) = ≈-refl
  [∘ˢ] (tm-meta M ts) = ≈-meta (λ i → [∘ˢ] (ts i))
  [∘ˢ] (tm-oper f es) = ≈-oper (λ i → ≈-trans ([]ˢ-resp-≈ˢ (es i) ⇑ˢ-resp-∘ˢ) ([∘ˢ] (es i)))

  -- Terms form a relative monad

  module _ where
    open Categories.Category
    open Categories.Functor using (Functor)
    open Categories.Category.Instance.Setoids
    open Categories.Monad.Relative
    open Function.Equality using () renaming (setoid to Π-setoid)
    open Categories.Category.Equivalence using (StrongEquivalence)
    open import SecondOrder.IndexedCategory
    open import SecondOrder.RelativeKleisli

    -- The embedding of contexts into setoids indexed by sorts

    slots : Functor VContexts (IndexedCategory sort (Setoids ℓ ℓ))
    slots = record
              { F₀ = λ Γ A → setoid (A ∈ Γ)
              ; F₁ = λ ρ A → record { _⟨$⟩_ = ρ ; cong = cong ρ }
              ; identity = λ A ξ → ξ
              ; homomorphism = λ {_} {_} {_} {ρ} {σ} A {_} {_} ξ → cong σ (cong ρ ξ)
              ; F-resp-≈ = λ ξ A ζ → trans (ξ _) (cong _ ζ)
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

    Term-Monad : Monad slots
    Term-Monad =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record
        { F₀ = Term-setoid Θ
        ; unit = λ A → record { _⟨$⟩_ = idˢ ; cong = λ ξ → ≈-≡ (cong idˢ ξ) }
        ; extend = λ σ A → record { _⟨$⟩_ =  [ (σ _ ⟨$⟩_) ]ˢ_ ; cong = []ˢ-resp-≈ (σ _ ⟨$⟩_)}
        ; identityʳ = λ {_} {_} {σ} A {_} {_} ξ → func-cong (σ A) ξ
        ; identityˡ = λ A → ≈-trans [idˢ]
        ; assoc = λ {_} {_} {_} {σ} {ρ} A {_} {t} ξ → ≈-trans ([]ˢ-resp-≈ _ ξ) ([∘ˢ] t)
        ; extend-≈ = λ {Γ} {Δ} {σ} {ρ} ζ B {s} {t} ξ → []ˢ-resp-≈ˢ-≈ (λ x → ζ _ refl) ξ
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
        ; assoc = λ {Γ} {Δ} {Ξ} {Ψ} {σ} {τ} {ψ} {A} x → [∘ˢ] (σ x)
        ; sym-assoc = λ {Γ} {Δ} {Ξ} {Ψ} {σ} {τ} {ψ} {A} x → ≈-sym ([∘ˢ] (σ x))
        ; identityˡ = λ x → [idˢ]
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
                         ; commute = λ σ A x≡y → [idˢ]-resp-≈ (≈-≡ (cong (λ x → σ A ⟨$⟩ x) x≡y))
                         ; sym-commute = λ σ A x≡y
                                       → ≈-sym ([idˢ]-resp-≈ (≈-≡ (cong (λ x → σ A ⟨$⟩ x ) (sym x≡y))))
                         }
                   ; F⇐G =
                         record
                         { η = λ Γ A → record { _⟨$⟩_ = idˢ
                                               ; cong = λ i≡j → ≈-≡ (cong idˢ i≡j)
                                               }
                         ; commute = λ σ A x≡y → [idˢ]-resp-≈ (≈-≡ (cong (λ x → σ A ⟨$⟩ x) x≡y))
                         ; sym-commute = λ σ A x≡y
                                       → ≈-sym ([idˢ]-resp-≈ (≈-≡ (cong (λ x → σ A ⟨$⟩ x ) (sym x≡y))))
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
                         ; commute = λ σ x → [idˢ]
                         ; sym-commute = λ σ x → ≈-sym [idˢ]
                         }
                   ; F⇐G =
                         record
                         { η = λ Γ x → tm-var x
                         ; commute = λ σ x → [idˢ]
                         ; sym-commute = λ σ x → ≈-sym [idˢ]
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
