open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; setoid)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; zip; map; <_,_>; swap)
import Function.Equality
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

import Categories.Category
import Categories.Functor
import Categories.Category.Instance.Setoids
import Categories.Monad.Relative
import Categories.Category.Equivalence
import Categories.Category.Cocartesian
import Categories.Category.Construction.Functors
import Categories.Category.Product
import Categories.NaturalTransformation
import Categories.NaturalTransformation.NaturalIsomorphism

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.VRenaming
import SecondOrder.MRenaming
import SecondOrder.Term
import SecondOrder.Substitution
import SecondOrder.RMonadsMorphism
import SecondOrder.Instantiation
import SecondOrder.IndexedCategory
import SecondOrder.RelativeKleisli
import SecondOrder.Mslot


module SecondOrder.MRelMon
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.VRenaming Σ
  open SecondOrder.MRenaming Σ
  open SecondOrder.Mslot Σ
  open SecondOrder.Substitution Σ
  open SecondOrder.Instantiation Σ
  open import SecondOrder.RMonadsMorphism
  open Categories.Category
  open Categories.Functor using (Functor)
  open Categories.NaturalTransformation renaming (id to idNt)
  open Categories.NaturalTransformation.NaturalIsomorphism renaming (refl to reflNt; sym to symNt; trans to transNt)
  open Categories.Category.Construction.Functors
  open Categories.Category.Instance.Setoids
  open Categories.Category.Product
  open Function.Equality using () renaming (setoid to Π-setoid)
  open SecondOrder.IndexedCategory
  -- open import SecondOrder.RelativeKleisli

  module MTerm {Γ : VContext} where
    open Category
    open NaturalTransformation
    open Functor
    open Categories.Monad.Relative
    open Function.Equality using () renaming (setoid to Π-setoid)
    open Categories.Category.Equivalence using (StrongEquivalence)
    open SecondOrder.RelativeKleisli

    MMonad : Monad Mslots
    MMonad =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record
      { F₀ = λ Θ A →
           record
           { F₀ = λ Ψ → record
                          { F₀ = λ Δ → Term-setoid (Θ ,, Ψ) (Γ ,, Δ) A
                          ; F₁ = λ {Δ} {Ξ} ρ → record { _⟨$⟩_ = [_]ᵛ_ (ʳ⇑ᵛ ρ) ; cong = λ t≈s → []ᵛ-resp-≈ t≈s }
                          ; identity = λ t≈s → ≈-trans ([]ᵛ-resp-≡ᵛ idᵛ+idᵛ) (≈-trans [id]ᵛ t≈s)
                          ; homomorphism = λ t≈s → ≈-trans ([]ᵛ-resp-≈ t≈s) ∘ᵛ-resp-ʳ⇑ᵛ-term
                          ; F-resp-≈ = λ ρ≈τ t≈s → {!!}
                          }
           ; F₁ = λ ι → record
                         { η = λ Δ → record { _⟨$⟩_ = [_]ᵐʳ_ (ᵐʳ⇑ᵐʳ ι) ; cong = λ t≈s → []ᵐʳ-resp-≈ t≈s }
                         ; commute = λ ρ t≈s → ≈-trans ([]ᵐʳ-resp-≈ ([]ᵛ-resp-≈ t≈s)) vr-comm-mr
                         ; sym-commute = λ ρ t≈s → ≈-trans (≈-sym vr-comm-mr) ([]ᵐʳ-resp-≈ ([]ᵛ-resp-≈ t≈s))
                         }
           ; identity = λ t≈s → ≈-trans ([]ᵐʳ-resp-≈ t≈s) (≈-trans ([]ᵐʳ-resp-≡ᵐʳ ᵐʳ⇑ᵐʳid≡ᵐʳidᵐʳ) [id]ᵐʳ)
           ; homomorphism = λ t≈s → ≈-trans ([]ᵐʳ-resp-≈ t≈s) ∘ᵐʳ-resp-ᵐʳ⇑-term
           ; F-resp-≈ = λ ι≈μ t≈s → ≈-trans ([]ᵐʳ-resp-≈ t≈s) ([]ᵐʳ-resp-≡ᵐʳ (ᵐʳ⇑ᵐʳ-resp-≡ᵐʳ ι≈μ))
           }
      ; unit = λ A → record
                      { η = λ Θ →
                          record
                          { η = λ Δ → record { _⟨$⟩_ = [_]ᵛ_ inrᵛ ; cong = λ t≈s → []ᵛ-resp-≈ t≈s }
                          ; commute = λ ρ t≈s → ≈-trans ([]ᵛ-resp-≈ ([]ᵛ-resp-≈ t≈s)) (≈-sym ʳ⇑ᵛ-comm-inrᵛ-term)
                          ; sym-commute = λ ρ t≈s → ≈-trans ʳ⇑ᵛ-comm-inrᵛ-term ([]ᵛ-resp-≈ ([]ᵛ-resp-≈ t≈s))
                          }
                      ; commute = λ f t≈s → ≈-trans ([]ᵛ-resp-≈ ([]ᵐʳ-resp-≈ t≈s)) mr-comm-vr
                      ; sym-commute = λ f t≈s → ≈-trans ? ([]ᵛ-resp-≈ ([]ᵐʳ-resp-≈ t≈s))
                      }
      ; extend = λ I A → record
                          { η = λ Θ →
                              record
                              { η = λ Ψ → record { _⟨$⟩_ = [_]ⁱ_ {!!} ; cong = {!!} }
                              ; commute = {!!}
                              ; sym-commute = {!!}
                              }
                          ; commute = {!!}
                          ; sym-commute = {!!}
                          }
      ; identityʳ = {!!}
      ; identityˡ = {!!}
      ; assoc = {!!}
      ; extend-≈ = {!!}
      }
