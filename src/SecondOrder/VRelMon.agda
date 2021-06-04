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


  -- TERMS FORM A RELATIVE MONAD
  -- (FOR A FUNCTOR WHOSE DOMAIN IS THE
  -- CATEGORY OF VARIABLE CONTEXTS AND RENAMINGS)

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
        F₀ :  VContext → MContext → Obj
        F₁ : ∀ {Θ ψ Δ Ξ} (ρ : Δ ⇒ᵛʳ Ξ) (ι : Θ ⇒ᵐʳ ψ)
             → (F₀ Δ Θ) ⇒ (F₀ Ξ ψ)
        identity : ∀ {Θ Δ}
                   → Category._≈_ (Setoids ℓ ℓ) (F₁ (idᵛʳ {Δ}) (idᵐʳ {Θ})) (id {F₀ Δ Θ})
        homomorphism : ∀ {Θ ψ Ω Γ Δ Ξ} {ρ : Γ ⇒ᵛʳ Δ} {ι : Θ ⇒ᵐʳ ψ} {τ : Δ ⇒ᵛʳ Ξ} {μ : ψ ⇒ᵐʳ Ω}
                       → Category._≈_ (Setoids ℓ ℓ) (F₁ (τ ∘ᵛʳ ρ) (μ ∘ᵐʳ ι)) ((F₁ τ μ) ∘ (F₁ ρ ι))
        F-resp-≈ : ∀ {Θ ψ Γ Δ} {ρ τ : Γ ⇒ᵛʳ Δ} {ι μ : Θ ⇒ᵐʳ ψ}
                   → (ρ ≡ᵛʳ τ) → (ι ≡ᵐʳ μ) → (Category._≈_ (Setoids ℓ ℓ) (F₁ ρ ι) (F₁ τ μ))



    -- Transformation for Functors-Jⱽ (analogue to natural transformations)

    record NaturalTransformation-Jⱽ (Fⱽ Gⱽ : Functor-Jⱽ) : Set (lsuc ℓ)
      where
        private
          module Fⱽ = Functor-Jⱽ Fⱽ
          module Gⱽ = Functor-Jⱽ Gⱽ
        open Fⱽ using (F₀; F₁)
        open Category (Setoids ℓ ℓ)
        field
          η : ∀ Θ Γ → (F₀ Γ Θ) ⇒ (Gⱽ.F₀ Γ Θ)
          commute : ∀ {Θ ψ Γ Δ} (ρ : Γ ⇒ᵛʳ Δ) (ι : Θ ⇒ᵐʳ ψ)
                    → Category._≈_ (Setoids ℓ ℓ) ((η ψ Δ) ∘ (F₁ ρ ι)) ((Gⱽ.F₁ ρ ι) ∘ (η Θ Γ))

    open NaturalTransformation-Jⱽ



    -- Equivalence of NaturalTransformation-Jⱽ (analogue to the one
    -- of the natural transformations)

    infix 4 _≃Jⱽ_

    _≃Jⱽ_ : ∀ {Fⱽ Gⱽ : Functor-Jⱽ} → Rel (NaturalTransformation-Jⱽ Fⱽ Gⱽ) ℓ
    𝒩 ≃Jⱽ ℳ  = ∀ {Θ Γ} → Category._≈_ (Setoids ℓ ℓ)
                            (η 𝒩 Θ Γ)
                            (η ℳ Θ Γ)


    -- Identity transformation analogue to the one
    -- of the natural transformations, for NaturalTransformation-Jⱽ

    idN-Jⱽ : ∀ {Fⱽ : Functor-Jⱽ} → NaturalTransformation-Jⱽ Fⱽ Fⱽ
    idN-Jⱽ {Fⱽ} =
           record
             { η = λ Θ Γ →
               record
                 { _⟨$⟩_ = λ x → x
                 ; cong = λ x → x }
             ; commute = λ {Θ} {ψ} {Γ} {Δ} ρ ι ξ
                         → Functor-Jⱽ.F-resp-≈  Fⱽ {Θ} {ψ} {Γ} {Δ} {ρ} {ρ} {ι} {ι}
                                                (λ x₁ → refl) (λ M → refl) ξ }




    -- Composition of NaturalTransformation-Jⱽ (analogue to the one
    -- of the natural transformations)

    _∘-Jⱽ_ : ∀ {Fⱽ Gⱽ Hⱽ : Functor-Jⱽ} (𝒩 : NaturalTransformation-Jⱽ Gⱽ Hⱽ) (ℳ : NaturalTransformation-Jⱽ Fⱽ Gⱽ) → NaturalTransformation-Jⱽ Fⱽ Hⱽ
    _∘-Jⱽ_ {Fⱽ} {Gⱽ} {Hⱽ} 𝒩 ℳ =
             let open Category (Setoids ℓ ℓ) in
             let open NaturalTransformation-Jⱽ in
             let open Functor-Jⱽ in
             record
                 { η = λ Θ Γ → η 𝒩 Θ Γ ∘ η ℳ Θ Γ
                 ; commute = λ {Θ} {ψ} {Γ} {Δ} ρ ι →
                             let open HomReasoning {F₀ Fⱽ Γ Θ} {F₀ Hⱽ Δ ψ} in
                             begin
                             (Category._∘_ (Setoids ℓ ℓ) (η {Gⱽ} {Hⱽ} 𝒩 ψ Δ) ((η {Fⱽ} {Gⱽ} ℳ ψ Δ) ∘ (F₁ Fⱽ ρ ι))) ≈⟨ assoc {f = F₁ Fⱽ ρ ι} {g = η ℳ ψ Δ} {h = η 𝒩 ψ Δ} ⟩
                             (η 𝒩 ψ Δ ∘ (η ℳ ψ Δ) ∘ (F₁ Fⱽ ρ ι)) ≈⟨ refl⟩∘⟨_
                                                                      {f = η 𝒩 ψ Δ} {g = (η ℳ ψ Δ) ∘ (F₁ Fⱽ ρ ι)}
                                                                      {i = (F₁ Gⱽ ρ ι) ∘ (η ℳ Θ Γ)}
                                                                      (commute ℳ ρ ι) ⟩
                             (η 𝒩 ψ Δ ∘ ((F₁ Gⱽ ρ ι) ∘ (η ℳ Θ Γ))) ≈⟨ sym-assoc {f = η ℳ Θ Γ} {g = F₁ Gⱽ ρ ι} {h = η 𝒩 ψ Δ}⟩
                             ((η 𝒩 ψ Δ) ∘ (F₁ Gⱽ ρ ι)) ∘ (η ℳ Θ Γ) ≈⟨ _⟩∘⟨refl
                                                                      {f = (η 𝒩 ψ Δ) ∘ (F₁ Gⱽ ρ ι)} {h = (F₁ Hⱽ ρ ι) ∘ (η 𝒩 Θ Γ)}
                                                                      {g = η ℳ Θ Γ}
                                                                      (commute 𝒩 ρ ι) ⟩
                             (((F₁ Hⱽ ρ ι) ∘ (η 𝒩 Θ Γ)) ∘ (η ℳ Θ Γ)) ≈⟨ assoc {f = η ℳ Θ Γ} {g = η 𝒩 Θ Γ} {h = F₁ Hⱽ ρ ι} ⟩
                             (((F₁ Hⱽ ρ ι) ∘ (η 𝒩 Θ Γ)) ∘ (η ℳ Θ Γ)) ∎}



    -- Proof that the category of Functors-Jⱽ and NaturalTransformation-Jⱽ is indeed a category

    -- associativity of composition
    -- (surprisingly enough, the proof of "sym-assoc-Jⱽ" is exactly the same :
    -- Is there a problem in the definitions ?)
    assoc-Jⱽ : {A B C D : Functor-Jⱽ}
               {ℒ : NaturalTransformation-Jⱽ A B}
               {ℳ : NaturalTransformation-Jⱽ B C}
               {𝒩 : NaturalTransformation-Jⱽ C D}
               → ((𝒩 ∘-Jⱽ ℳ) ∘-Jⱽ ℒ) ≃Jⱽ (𝒩 ∘-Jⱽ (ℳ ∘-Jⱽ ℒ))
    assoc-Jⱽ  {A} {B} {C} {D} {ℒ} {ℳ} {𝒩} {Θ} {Γ} ξ = Function.Equality.Π.cong (η 𝒩 Θ Γ)
                                                          (Function.Equality.Π.cong (η ℳ Θ Γ)
                                                            (Function.Equality.cong (η ℒ Θ Γ) ξ))

    -- identity is identity
    identityˡ-Jⱽ : {A B : Functor-Jⱽ}
                  {𝒩 : NaturalTransformation-Jⱽ A B}
                  → (idN-Jⱽ ∘-Jⱽ 𝒩) ≃Jⱽ 𝒩
    identityˡ-Jⱽ  {𝒩 = 𝒩} {Θ = Θ} {Γ = Γ} ξ = Function.Equality.cong (η 𝒩 Θ Γ) ξ


    -- Codomain of Jⱽ (the category with Functor-Jⱽ as objects and NaturalTransformation-Jⱽ as maps)
    Functors-Jⱽ : Category (lsuc ℓ) (lsuc ℓ)  ℓ
    Functors-Jⱽ = record
                    { Obj = Functor-Jⱽ
                    ; _⇒_ = NaturalTransformation-Jⱽ
                    ; _≈_ = _≃Jⱽ_
                    ; id = idN-Jⱽ
                    ; _∘_ = _∘-Jⱽ_
                    ; assoc = λ {Fⱽ} {Gⱽ} {Hⱽ} {Kⱽ} {𝒩} {ℳ} {ℒ} → assoc-Jⱽ  {ℒ = 𝒩} {ℳ = ℳ} {𝒩 = ℒ}
                    ; sym-assoc = λ {Fⱽ} {Gⱽ} {Hⱽ} {Kⱽ} {𝒩} {ℳ} {ℒ} → assoc-Jⱽ  {ℒ = 𝒩} {ℳ = ℳ} {𝒩 = ℒ}
                    ; identityˡ = λ {Fⱽ} {Gⱽ} {𝒩} → identityˡ-Jⱽ {𝒩 = 𝒩}
                    ; identityʳ = λ {Fⱽ} {Gⱽ} {𝒩} → identityˡ-Jⱽ {𝒩 = 𝒩}
                    ; identity² = λ {Fⱽ} ξ → ξ
                    ; equiv = λ {Fⱽ} {Gⱽ}
                              → record
                                  { refl = λ {𝒩 = 𝒩} {Θ = Θ} {Γ = Γ} {x} {y} ξ
                                           → Function.Equality.cong (η 𝒩 Θ Γ) ξ
                                  ; sym = λ {𝒩} {ℳ} ξᴺ {Θ} {Γ} ξ
                                          → Category.Equiv.sym (Setoids ℓ ℓ)
                                          {_} {_} {η 𝒩 Θ Γ} {η ℳ Θ Γ} ξᴺ ξ
                                  ; trans =  λ {𝒩} {ℳ} {ℒ} ξᴺ₂ ξᴺ₁ {Θ} {Γ} ξ
                                             → Category.Equiv.trans (Setoids ℓ ℓ)
                                             {_} {_} {η 𝒩 Θ Γ} {η ℳ Θ Γ} {η ℒ Θ Γ} ξᴺ₂ ξᴺ₁ ξ}
                    ; ∘-resp-≈ = λ {Fⱽ} {Gⱽ} {Hⱽ} {𝒩} {ℳ} {ℒ} {𝒦} ξᴺ₁ ξᴺ₂ {Θ} {Γ} ξ
                                 → Category.∘-resp-≈ (Setoids ℓ ℓ)
                                   {_} {_}  {_}
                                   {η 𝒩 Θ Γ} {η ℳ Θ Γ} {η ℒ Θ Γ} {η 𝒦 Θ Γ}
                                   ξᴺ₁ ξᴺ₂ ξ
                    }



    -- The embedding of contexts into setoids indexed by sorts, metavariable telescope and variable telescope

    Jⱽ : Functor VContexts (IndexedCategory sort Functors-Jⱽ)
    Jⱽ = record
              { F₀ = λ Γ A →
                       record
                         { F₀ = λ Δ Θ → setoid (A ∈ (Γ ,, Δ))
                         ; F₁ = λ ρ ι → record
                                            { _⟨$⟩_ = [ inlᵛʳ , inrᵛʳ ∘ᵛʳ ρ ]ᵛʳ
                                            ; cong = λ {x} {y} ξ →  ρ-resp-≡ {ρ = [ var-inl , var-inr ∘ᵛʳ ρ ]ᵛʳ} ξ}
                         ; identity = λ {Θ} {Δ} {x} ξ → trans (idᵛʳ+idᵛʳ x) ξ
                         ; homomorphism = λ {Θ} {ψ} {Ω} {Δ} {Ξ} {Λ} {ρ} {ι} {τ} {μ} {x} {y} ξ
                                          → trans
                                            (ʳ⇑ᵛʳ-∘ᵛʳ x)
                                            (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛʳ}
                                              (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (ρ x₁)) ]ᵛʳ} ξ))
                         ; F-resp-≈ = λ {Θ} {ψ} {Δ} {Ξ} {ρ} {τ} {ι} {μ} ξᵛʳ ξᵐʳ {x} {y} ξ
                                      → trans
                                        ([,]ᵛʳ-resp-≡ᵛʳ (λ x₁ → refl) (∘ᵛʳ-resp-≡ᵛʳ {τ₁ = λ x₁ → var-inr x₁} (λ x₁ → refl) λ x₁ → ξᵛʳ x₁) x)
                                        (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛʳ} ξ)
                         }

              ; F₁ = λ ρ A → record
                               { η = λ Θ Γ → record { _⟨$⟩_ = ⇑ᵛʳ ρ ; cong = cong (⇑ᵛʳ ρ) }
                               ; commute = λ τ ι {x} ξ
                                           → trans
                                             (uniqueᵛʳ²
                                               {τ = [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛʳ ∘ᵛʳ [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛʳ}
                                               {σ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛʳ ∘ᵛʳ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛʳ} (λ x₁ → refl) (λ x₁ → refl) x)
                                               (ρ-resp-≡
                                                 {ρ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛʳ ∘ᵛʳ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛʳ} ξ)}

              ; identity =  λ A {Θ} {Γ} {x} ξ → trans (idᵛʳ+idᵛʳ x) ξ
              ; homomorphism = λ {Δ} {Ξ} {Λ} {ρ} {τ} A {_} {_} {x} ξ
                               → trans
                                 (uniqueᵛʳ²
                                   {τ = [ (λ x₁ → var-inl (τ (ρ x₁))) , (λ x₁ → var-inr x₁) ]ᵛʳ}
                                   {σ = [ (λ x₁ → var-inl (τ x₁)) , (λ x₁ → var-inr x₁) ]ᵛʳ ∘ᵛʳ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛʳ}
                                   (λ x₁ → refl) (λ x₁ → refl) x)
                                 (ρ-resp-≡
                                   {ρ = [ (λ x₁ → var-inl (τ x₁)) , (λ x₁ → var-inr x₁) ]ᵛʳ ∘ᵛʳ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛʳ } ξ)
              ; F-resp-≈ = λ {_} {_} {ρ} {τ} ξρ A {_} {_} {x} {y} ξ
                           → trans
                             (([,]ᵛʳ-resp-≡ᵛʳ {ρ₁ = λ x₁ → var-inl (ρ x₁)} {τ₁ = var-inr} (λ x₁ → ∘ᵛʳ-resp-≡ᵛʳ {τ₁ = var-inl} (λ x₃ → refl) ξρ x₁) (λ x₁ → refl) x))
                             (ρ-resp-≡ {ρ = ⇑ᵛʳ τ} ξ)
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
    open NaturalTransformation-Jⱽ

    VMonad : Monad Jⱽ
    VMonad =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record
        { F₀ = λ Γ A → record
                         { F₀ = λ Δ ψ → Term-setoid Θ (Γ ,, Δ) A
                         ; F₁ = λ ρ ι → record { _⟨$⟩_ = [_]ᵛʳ_ (ʳ⇑ᵛʳ ρ) ; cong = λ ξ → []ᵛʳ-resp-≈ ξ }
                         ; identity = λ ξ → ≈-trans ([]ᵛʳ-resp-≡ᵛʳ idᵛʳ+idᵛʳ) (≈-trans [id]ᵛʳ ξ)
                         ; homomorphism = λ {_} {_} {_} {_} {_} {_} {ρ} {_} {τ} ξ
                                          → ≈-trans
                                          ([]ᵛʳ-resp-≈ ξ)
                                          (≈-trans
                                            ([]ᵛʳ-resp-≡ᵛʳ λ x₁
                                              → uniqueᵛʳ²
                                                {τ = [ (λ x₂ → var-inl x₂) , (λ x₂ → var-inr (τ (ρ x₂))) ]ᵛʳ}
                                                {σ = [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (τ x₁)) ]ᵛʳ  ∘ᵛʳ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (ρ x₁)) ]ᵛʳ }
                                                (λ x₂ → refl) (λ x₂ → refl) x₁)
                                            [∘]ᵛʳ)

                         ; F-resp-≈ = λ ξᵛʳ ξᵐʳ ξ → ≈-trans ([]ᵛʳ-resp-≈ ξ) ([]ᵛʳ-resp-≡ᵛʳ λ x → [,]ᵛʳ-resp-≡ᵛʳ (λ x₁ → refl) (λ x₁ → ρ-resp-≡ {ρ = var-inr} (ξᵛʳ x₁)) x )
                         }
        ; unit = λ A
                   → record
                     { η = λ ψ Γ
                       → record
                         { _⟨$⟩_ = λ x → tm-var x
                         ; cong = λ ξ → congˢ-var {σ = tm-var} ξ }
                       ; commute = λ ρ ι ξ → congˢ-var {σ = tm-var} (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (ρ x₁)) ]ᵛʳ} ξ) }
        ; extend = {!!}
        ; identityʳ = λ A ξ → {!!}
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
