-- {-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc; _⊔_ ;Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; setoid; cong; trans)
import Function.Equality
open import Relation.Binary using (Setoid)

import Categories.Category
import Categories.Functor
import Categories.Category.Instance.Setoids
import Categories.Monad.Relative
import Categories.Category.Equivalence
import Categories.Category.Cocartesian
import Categories.Category.Construction.Functors
import Categories.NaturalTransformation.Equivalence
import Relation.Binary.Core

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.VRenaming
import SecondOrder.MRenaming
import SecondOrder.Term
import SecondOrder.IndexedCategory
import SecondOrder.RelativeKleisli
import SecondOrder.Substitution

module SecondOrder.VRelMon
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.VRenaming Σ
  open SecondOrder.MRenaming Σ
  open SecondOrder.Substitution Σ


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
    open Categories.Category.Construction.Functors
    open Categories.NaturalTransformation.Equivalence
    open Relation.Binary.Core hiding (_⇒_)

    -- The carrier of the codomain of Jⱽ (morally ∀ Γ → A ∈ Δ ,, Γ)

    record Functor-Jⱽ : Set ((lsuc ℓ)) where
      open Category (Setoids ℓ ℓ)
      open Setoid
      field
        F₀ :  VContext → MContext → sort → Obj -- Obj (IndexedCategory sort (Setoids (lsuc ℓ) (lsuc ℓ)))
        F₁ : ∀ {Θ ψ Δ Ξ} (ρ : Δ ⇒ᵛʳ Ξ) (ι : Θ ⇒ᵐʳ ψ)  (A : sort)
             → (F₀ Δ Θ A) ⇒ (F₀ Ξ ψ A)
        identity : ∀ {Θ Δ A}
                   → Category._≈_ (Setoids ℓ ℓ) (F₁ (idᵛʳ {Δ}) (idᵐʳ {Θ}) A) (id {F₀ Δ Θ A})
        homomorphism : ∀ {Θ ψ Ω Γ Δ Ξ A} {ρ : Γ ⇒ᵛʳ Δ} {ι : Θ ⇒ᵐʳ ψ} {τ : Δ ⇒ᵛʳ Ξ} {μ : ψ ⇒ᵐʳ Ω}
                       → Category._≈_ (Setoids ℓ ℓ) (F₁ (τ ∘ᵛʳ ρ) (μ ∘ᵐʳ ι) A) ((F₁ τ μ A) ∘ (F₁ ρ ι A))
        F-resp-≈ : ∀ {Θ ψ Γ Δ A} {ρ τ : Γ ⇒ᵛʳ Δ} {ι μ : Θ ⇒ᵐʳ ψ}
                   → (ρ ≡ᵛʳ τ) → (ι ≡ᵐʳ μ) → (Category._≈_ (Setoids ℓ ℓ) (F₁ ρ ι A) (F₁ τ μ A))

    -- definition of transformation analogue to natural transformations, for Functors-Jⱽ

    record NaturalTransformation-Jⱽ (Fⱽ Gⱽ : Functor-Jⱽ) : Set (lsuc ℓ)
      where
        private
          module Fⱽ = Functor-Jⱽ Fⱽ
          module Gⱽ = Functor-Jⱽ Gⱽ
        open Fⱽ using (F₀; F₁)
        open Category (Setoids ℓ ℓ)
        field
          η : ∀ Θ Γ A → (F₀ Γ Θ A) ⇒ (Gⱽ.F₀ Γ Θ A)
          commute : ∀ {Θ ψ Γ Δ A} (ρ : Γ ⇒ᵛʳ Δ) (ι : Θ ⇒ᵐʳ ψ)
                    → Category._≈_ (Setoids ℓ ℓ) ((η ψ Δ A) ∘ (F₁ ρ ι A)) ((Gⱽ.F₁ ρ ι A) ∘ (η Θ Γ A))


    -- definition of an equivalence of transformation analogue to the one
    -- of the natural transformations, for NaturalTransformation-Jⱽ

    infix 4 _≃Jⱽ_

    _≃Jⱽ_ : ∀ {Fⱽ Gⱽ : Functor-Jⱽ} → Rel (NaturalTransformation-Jⱽ Fⱽ Gⱽ) ℓ
    𝒩 ≃Jⱽ ℳ  = ∀ {Θ Γ A} → Category._≈_ (Setoids ℓ ℓ)
                            (NaturalTransformation-Jⱽ.η 𝒩 Θ Γ A)
                            (NaturalTransformation-Jⱽ.η ℳ Θ Γ A)


    -- definition of an identityt transformation analogue to the one
    -- of the natural transformations, for NaturalTransformation-Jⱽ

    idN-Jⱽ : ∀ {A : Functor-Jⱽ} → NaturalTransformation-Jⱽ A A
    idN-Jⱽ =
           record
             { η = λ Θ Γ A →
               record
                 { _⟨$⟩_ = λ x → x
                 ; cong = λ x → x }
             ; commute = {!!} }

    -- Codomain of Jⱽ (the category with Functor-Jⱽ as objects and NaturalTransformation-Jⱽ as maps)
    Functors-Jⱽ : Category (lsuc ℓ) (lsuc ℓ)  ℓ
    Functors-Jⱽ = record
                    { Obj = Functor-Jⱽ
                    ; _⇒_ = NaturalTransformation-Jⱽ
                    ; _≈_ = _≃Jⱽ_
                    ; id = idN-Jⱽ
                    ; _∘_ = {!!}
                    ; assoc = {!!}
                    ; sym-assoc = {!!}
                    ; identityˡ = {!!}
                    ; identityʳ = {!!}
                    ; identity² = {!!}
                    ; equiv = {!!}
                    ; ∘-resp-≈ = {!!}
                    }

    -- The embedding of contexts into setoids indexed by sorts, metavariable telescope and variable telescope

    Jⱽ : Functor VContexts (Functors-Jⱽ)
    Jⱽ = record
              { F₀ = λ Γ →
                       record
                         { F₀ = λ Δ Θ A → setoid (A ∈ (Γ ,, Δ))
                         ; F₁ = λ ρ ι A → record
                                            { _⟨$⟩_ = [ inlᵛʳ , inrᵛʳ ∘ᵛʳ ρ ]ᵛʳ
                                            ; cong = λ {x} {y} ξ →  ρ-resp-≡ {ρ = [ var-inl , var-inr ∘ᵛʳ ρ ]ᵛʳ} ξ}
                         ; identity = {!!}
                         ; homomorphism = {!!}
                         ; F-resp-≈ = {!!}
                         }
              ; F₁ = {!!} -- λ ρ A → record { _⟨$⟩_ = ρ ; cong = cong ρ }
              ; identity = {!!} -- λ A ξ → ξ
              ; homomorphism = {!!} -- λ {_} {_} {_} {ρ} {σ} A {_} {_} ξ → cong σ (cong ρ ξ)
              ; F-resp-≈ = {!!} -- λ ξ A ζ → trans (ξ _) (cong _ ζ)
              }


  -- The relative monad over Jⱽ
  module _ {Θ : MContext} where
    open Categories.Category
    open Categories.Functor using (Functor)
    open Categories.Category.Instance.Setoids
    open Categories.Monad.Relative
    open Function.Equality using () renaming (setoid to Π-setoid)
    open Categories.Category.Equivalence using (StrongEquivalence)
    open import SecondOrder.IndexedCategory
    open import SecondOrder.RelativeKleisli

    VMonad : Monad Jⱽ
    VMonad =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record
        { F₀ = {!!}
        ; unit = {!!}
        ; extend = {!!}
        ; identityʳ = {!!}
        ; identityˡ = {!!}
        ; assoc = {!!}
        ; extend-≈ = {!!}
        }




    -- Other possibility, if the above doesn't work :

    -- Jⱽ′ : Functor VContexts (Functors MContexts (Functors VContexts (IndexedCategory sort (Setoids ℓ ℓ))))
    -- Jⱽ′ = record
    --           { F₀ = {!!} -- λ Γ A → setoid (A ∈ Γ)
    --           ; F₁ = {!!} -- λ ρ A → record { _⟨$⟩_ = ρ ; cong = cong ρ }
    --           ; identity = {!!} -- λ A ξ → ξ
    --           ; homomorphism = {!!} -- λ {_} {_} {_} {ρ} {σ} A {_} {_} ξ → cong σ (cong ρ ξ)
    --           ; F-resp-≈ = {!!} -- λ ξ A ζ → trans (ξ _) (cong _ ζ)
    --           }
