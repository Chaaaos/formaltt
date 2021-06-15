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

    record Codomain-Jⱽ-Elt : Set ((lsuc ℓ)) where
      open Category (Setoids ℓ ℓ)
      open Setoid
      field
        F₀ :  VContext → MContext → Obj
        F₁ : ∀ {Θ ψ Δ Ξ} (ρ : Δ ⇒ᵛ Ξ) (ι : Θ ⇒ᵐ ψ)
             → (F₀ Δ Θ) ⇒ (F₀ Ξ ψ)
        identity : ∀ {Θ Δ}
                   → Category._≈_ (Setoids ℓ ℓ) (F₁ (idᵛ {Δ}) (idᵐ {Θ})) (id {F₀ Δ Θ})
        homomorphism : ∀ {Θ ψ Ω Γ Δ Ξ} {ρ : Γ ⇒ᵛ Δ} {ι : Θ ⇒ᵐ ψ} {τ : Δ ⇒ᵛ Ξ} {μ : ψ ⇒ᵐ Ω}
                       → Category._≈_ (Setoids ℓ ℓ) (F₁ (τ ∘ᵛ ρ) (μ ∘ᵐ ι)) ((F₁ τ μ) ∘ (F₁ ρ ι))
        F-resp-≈ : ∀ {Θ ψ Γ Δ} {ρ τ : Γ ⇒ᵛ Δ} {ι μ : Θ ⇒ᵐ ψ}
                   → (ρ ≡ᵛ τ) → (ι ≡ᵐ μ) → (Category._≈_ (Setoids ℓ ℓ) (F₁ ρ ι) (F₁ τ μ))



    -- Transformation for Codomain-Jⱽ (analogue to natural transformations)

    record NaturalTransformation-Jⱽ (Fⱽ Gⱽ : Codomain-Jⱽ-Elt) : Set (lsuc ℓ)
      where
        private
          module Fⱽ = Codomain-Jⱽ-Elt Fⱽ
          module Gⱽ = Codomain-Jⱽ-Elt Gⱽ
        open Fⱽ using (F₀; F₁)
        open Category (Setoids ℓ ℓ)
        field
          η : ∀ Θ Γ → (F₀ Γ Θ) ⇒ (Gⱽ.F₀ Γ Θ)
          commute : ∀ {Θ ψ Γ Δ} (ρ : Γ ⇒ᵛ Δ) (ι : Θ ⇒ᵐ ψ)
                    → Category._≈_ (Setoids ℓ ℓ) ((η ψ Δ) ∘ (F₁ ρ ι)) ((Gⱽ.F₁ ρ ι) ∘ (η Θ Γ))
          -- ignore-MCtx : ∀ Θ Ω Γ → (∀ (x : F₀ Γ Θ))

    open NaturalTransformation-Jⱽ



    -- Equivalence of NaturalTransformation-Jⱽ (analogue to the one
    -- of the natural transformations)

    infix 4 _≃Jⱽ_

    _≃Jⱽ_ : ∀ {Fⱽ Gⱽ : Codomain-Jⱽ-Elt} → Rel (NaturalTransformation-Jⱽ Fⱽ Gⱽ) ℓ
    𝒩 ≃Jⱽ ℳ  = ∀ {Θ Γ} → Category._≈_ (Setoids ℓ ℓ)
                            (η 𝒩 Θ Γ)
                            (η ℳ Θ Γ)


    -- Identity transformation analogue to the one
    -- of the natural transformations, for NaturalTransformation-Jⱽ

    idN-Jⱽ : ∀ {Fⱽ : Codomain-Jⱽ-Elt} → NaturalTransformation-Jⱽ Fⱽ Fⱽ
    idN-Jⱽ {Fⱽ} =
           record
             { η = λ Θ Γ →
               record
                 { _⟨$⟩_ = λ x → x
                 ; cong = λ x → x }
             ; commute = λ {Θ} {ψ} {Γ} {Δ} ρ ι ξ
                         → Codomain-Jⱽ-Elt.F-resp-≈  Fⱽ {Θ} {ψ} {Γ} {Δ} {ρ} {ρ} {ι} {ι}
                                                (λ x₁ → refl) (λ M → refl) ξ }




    -- Composition of NaturalTransformation-Jⱽ (analogue to the one
    -- of the natural transformations)

    _∘-Jⱽ_ : ∀ {Fⱽ Gⱽ Hⱽ : Codomain-Jⱽ-Elt} (𝒩 : NaturalTransformation-Jⱽ Gⱽ Hⱽ) (ℳ : NaturalTransformation-Jⱽ Fⱽ Gⱽ) → NaturalTransformation-Jⱽ Fⱽ Hⱽ
    _∘-Jⱽ_ {Fⱽ} {Gⱽ} {Hⱽ} 𝒩 ℳ =
             let open Category (Setoids ℓ ℓ) in
             let open NaturalTransformation-Jⱽ in
             let open Codomain-Jⱽ-Elt in
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



    -- Proof that the category of Codomain-Jⱽ and NaturalTransformation-Jⱽ is indeed a category

    -- associativity of composition
    -- (surprisingly enough, the proof of "sym-assoc-Jⱽ" is exactly the same :
    -- Is there a problem in the definitions ?)
    assoc-Jⱽ : {A B C D : Codomain-Jⱽ-Elt}
               {ℒ : NaturalTransformation-Jⱽ A B}
               {ℳ : NaturalTransformation-Jⱽ B C}
               {𝒩 : NaturalTransformation-Jⱽ C D}
               → ((𝒩 ∘-Jⱽ ℳ) ∘-Jⱽ ℒ) ≃Jⱽ (𝒩 ∘-Jⱽ (ℳ ∘-Jⱽ ℒ))
    assoc-Jⱽ  {A} {B} {C} {D} {ℒ} {ℳ} {𝒩} {Θ} {Γ} ξ = Function.Equality.Π.cong (η 𝒩 Θ Γ)
                                                          (Function.Equality.Π.cong (η ℳ Θ Γ)
                                                            (Function.Equality.cong (η ℒ Θ Γ) ξ))

    -- identity is identity
    identityˡ-Jⱽ : {A B : Codomain-Jⱽ-Elt}
                  {𝒩 : NaturalTransformation-Jⱽ A B}
                  → (idN-Jⱽ ∘-Jⱽ 𝒩) ≃Jⱽ 𝒩
    identityˡ-Jⱽ  {𝒩 = 𝒩} {Θ = Θ} {Γ = Γ} ξ = Function.Equality.cong (η 𝒩 Θ Γ) ξ


    -- Codomain of Jⱽ (the category with Codomain-Jⱽ-Elt as objects and NaturalTransformation-Jⱽ as maps)
    Codomain-Jⱽ : Category (lsuc ℓ) (lsuc ℓ)  ℓ
    Codomain-Jⱽ = record
                    { Obj = Codomain-Jⱽ-Elt
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

    Jⱽ : Functor VContexts (IndexedCategory sort Codomain-Jⱽ)
    Jⱽ = record
              { F₀ = λ Γ A →
                       record
                         { F₀ = λ Δ Θ → setoid (A ∈ (Γ ,, Δ))
                         ; F₁ = λ ρ ι → record
                                            { _⟨$⟩_ = [ inlᵛ , inrᵛ ∘ᵛ ρ ]ᵛ
                                            ; cong = λ {x} {y} ξ →  ρ-resp-≡ {ρ = [ var-inl , var-inr ∘ᵛ ρ ]ᵛ} ξ}
                         ; identity = λ {Θ} {Δ} {x} ξ → trans (idᵛ+idᵛ x) ξ
                         ; homomorphism = λ {Θ} {ψ} {Ω} {Δ} {Ξ} {Λ} {ρ} {ι} {τ} {μ} {x} {y} ξ
                                          → trans
                                            (ʳ⇑ᵛ-resp-∘ᵛ x)
                                            (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ}
                                              (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (ρ x₁)) ]ᵛ} ξ))
                         ; F-resp-≈ = λ {Θ} {ψ} {Δ} {Ξ} {ρ} {τ} {ι} {μ} ξᵛ ξᵐ {x} {y} ξ
                                      → trans
                                        ([,]ᵛ-resp-≡ᵛ (λ x₁ → refl) (∘ᵛ-resp-≡ᵛ {τ₁ = λ x₁ → var-inr x₁} (λ x₁ → refl) λ x₁ → ξᵛ x₁) x)
                                        (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ} ξ)
                         }

              ; F₁ = λ ρ A → record
                               { η = λ Θ Γ → record { _⟨$⟩_ = ⇑ᵛ ρ ; cong = cong (⇑ᵛ ρ) }
                               ; commute = λ τ ι {x} ξ
                                           → trans
                                             (uniqueᵛ²
                                               {τ = [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ ∘ᵛ [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ}
                                               {σ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ ∘ᵛ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ} (λ x₁ → refl) (λ x₁ → refl) x)
                                               (ρ-resp-≡
                                                 {ρ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ ∘ᵛ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ} ξ)}

              ; identity =  λ A {Θ} {Γ} {x} ξ → trans (idᵛ+idᵛ x) ξ
              ; homomorphism = λ {Δ} {Ξ} {Λ} {ρ} {τ} A {_} {_} {x} ξ
                               → trans
                                 (uniqueᵛ²
                                   {τ = [ (λ x₁ → var-inl (τ (ρ x₁))) , (λ x₁ → var-inr x₁) ]ᵛ}
                                   {σ = [ (λ x₁ → var-inl (τ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ ∘ᵛ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ}
                                   (λ x₁ → refl) (λ x₁ → refl) x)
                                 (ρ-resp-≡
                                   {ρ = [ (λ x₁ → var-inl (τ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ ∘ᵛ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ } ξ)
              ; F-resp-≈ = λ {_} {_} {ρ} {τ} ξρ A {_} {_} {x} {y} ξ
                           → trans
                             (([,]ᵛ-resp-≡ᵛ {ρ₁ = λ x₁ → var-inl (ρ x₁)} {τ₁ = var-inr} (λ x₁ → ∘ᵛ-resp-≡ᵛ {τ₁ = var-inl} (λ x₃ → refl) ξρ x₁) (λ x₁ → refl) x))
                             (ρ-resp-≡ {ρ = ⇑ᵛ τ} ξ)
              }

  factor-empty-ctx : ∀ {Θ Ω Γ Δ A} (x : Setoid.Carrier ((Codomain-Jⱽ-Elt.F₀((Categories.Functor.Functor.F₀ Jⱽ) Γ A)) Δ Θ)) → x ≡ ((NaturalTransformation-Jⱽ.η ((NaturalTransformation-Jⱽ.η (Categories.Functor.Functor.F₁ Jⱽ)) ? A)) Ω Γ x)
  factor-empty-ctx = ?

  -- The relative monad over Jⱽ

  module _ {Θ : MContext} where
    open Categories.Category
    open Categories.Functor using (Functor)
    open Categories.Category.Instance.Setoids
    open Categories.Category.Category (Setoids ℓ ℓ)
    open Categories.Monad.Relative
    open Function.Equality using () renaming (setoid to Π-setoid)
    open Categories.Category.Equivalence using (StrongEquivalence)
    open import SecondOrder.IndexedCategory
    open import SecondOrder.RelativeKleisli
    open NaturalTransformation-Jⱽ
    open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong)
    open import Relation.Binary.Reasoning.MultiSetoid

    -- Setoids≈-⟨$⟩ : ∀ {From To} (f g : From Function.Equality.⟶ To) → (Category._≈_ (Setoids ℓ ℓ) f g) → (∀ (x : Setoid.Carrier From) → Setoid._≈_ To (f ⟨$⟩ x) (g ⟨$⟩ x))
    -- Setoids≈-⟨$⟩ = {!!}

    VMonad : Monad Jⱽ
    Codomain-Jⱽ-Elt.F₀ (Monad.F₀ VMonad Γ A) Δ ψ = Term-setoid Θ (Γ ,, Δ) A
    _⟨$⟩_      (Codomain-Jⱽ-Elt.F₁ (Monad.F₀ VMonad Γ A) ρ ι) = [ ʳ⇑ᵛ ρ ]ᵛ_
    func-cong (Codomain-Jⱽ-Elt.F₁ (Monad.F₀ VMonad Γ A) ρ ι) ξ = []ᵛ-resp-≈ ξ
    Codomain-Jⱽ-Elt.identity     (Monad.F₀ VMonad Γ A) ξ = ≈-trans ([]ᵛ-resp-≡ᵛ idᵛ+idᵛ) (≈-trans [idᵛ] ξ)
    Codomain-Jⱽ-Elt.homomorphism (Monad.F₀ VMonad Γ A) {ρ = ρ} {ι = ι} {τ = τ} {μ = μ} {x = x} {y = y} ξ
      = begin⟨ Term-setoid Θ _ _ ⟩
          [ ʳ⇑ᵛ (τ ∘ᵛ ρ) ]ᵛ x ≈⟨ []ᵛ-resp-≈ ξ ⟩
          [ ʳ⇑ᵛ (τ ∘ᵛ ρ) ]ᵛ y ≈⟨ []ᵛ-resp-≡ᵛ (λ x₁ →
              uniqueᵛ² {τ = [ (λ x₂ → var-inl x₂) , (λ x₂ → var-inr (τ (ρ x₂))) ]ᵛ}
                       {σ = σ' }
                       (λ x₂ → refl) (λ x₂ → refl) x₁) ⟩
          [ σ' ]ᵛ y ≈⟨ [∘ᵛ] ⟩
         ((Codomain-Jⱽ-Elt.F₁ (Monad.F₀ VMonad Γ A) τ μ ∘
           Codomain-Jⱽ-Elt.F₁ (Monad.F₀ VMonad Γ A) ρ ι) ⟨$⟩ y)
         ∎
         where
           σ' : (Γ ,, _) ⇒ᵛ Γ ,, _
           σ' = [ var-inl
                , (λ x₁ → var-inr (τ x₁))
                ]ᵛ ∘ᵛ [ var-inl
                      , (λ x₁ → var-inr (ρ x₁))
                      ]ᵛ
    Codomain-Jⱽ-Elt.F-resp-≈  (Monad.F₀ VMonad Γ A) {ψ} {Ω} {Δ} {Ξ} {ρ} {τ} {ι} {μ} ξᵛ ξᵐ {t} {u} ξ  =
                                                          begin⟨ Term-setoid Θ _ _ ⟩
                                                          ([ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (ρ x₁)) ]ᵛ ]ᵛ t) ≈⟨ []ᵛ-resp-≈ ξ ⟩
                                                          ([ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (ρ x₁)) ]ᵛ ]ᵛ u)
                                                                                   ≈⟨ []ᵛ-resp-≡ᵛ ([,]ᵛ-resp-≡ᵛ (λ x → refl) λ x → ρ-resp-≡ {ρ = var-inr} (ξᵛ x)) ⟩
                                                          ([ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (τ x₁)) ]ᵛ ]ᵛ u) ∎

    _⟨$⟩_ (η (Monad.unit VMonad A) ψ Γ) = tm-var
    func-cong (η (Monad.unit VMonad A) ψ Γ) ξ = congˢ-var {σ = tm-var} ξ
    commute (Monad.unit VMonad A) ρ ι ξ =  congˢ-var {σ = tm-var} (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (ρ x₁)) ]ᵛ} ξ)

    _⟨$⟩_   (η (Monad.extend VMonad {Δ} {Ξ} σ A) ψ Γ) t = [ (λ {B} x →  η (σ B) Θ Γ  ⟨$⟩ x) ]ˢ t
    func-cong (η (Monad.extend VMonad σ A) ψ Γ) = []ˢ-resp-≈ ((λ {B} x → η (σ B) Θ Γ ⟨$⟩ x) )
    commute (Monad.extend VMonad {Υ} {Ω} σ A) {Ξ} {Ψ} {Γ} {Δ} ρ ι {x} {y} x≈y
      = begin⟨ Term-setoid Θ _ _ ⟩
        (η (Monad.extend VMonad σ A) Ψ Δ ∘
          Codomain-Jⱽ-Elt.F₁ (Monad.F₀ VMonad Υ A) ρ ι
          ⟨$⟩ x)
          ≈⟨ ≈-sym ([ˢ∘ᵛ] x) ⟩
        ([ (λ {B} x₁ → η (σ B) Θ Δ ⟨$⟩ x₁) ˢ∘ᵛ (ʳ⇑ᵛ ρ) ]ˢ x) ≈⟨ []ˢ-resp-≈ ((λ {B} → _⟨$⟩_ (η (σ B) Θ Δ)) ˢ∘ᵛ(ʳ⇑ᵛ ρ)) x≈y ⟩
        ([ (λ {B} → _⟨$⟩_ (η (σ B) Θ Δ)) ˢ∘ᵛ (ʳ⇑ᵛ ρ) ]ˢ y) ≈⟨ []ˢ-resp-≈ˢ y (η-ˢ∘ᵛ ρ ι) ⟩
        ([ ʳ⇑ᵛ ρ ᵛ∘ˢ (λ {B} x₁ → η (σ B) Θ Γ ⟨$⟩ x₁) ]ˢ y) ≈⟨ [ᵛ∘ˢ] y ⟩
        (Codomain-Jⱽ-Elt.F₁ (Monad.F₀ VMonad Ω A) ρ ι ∘
          η (Monad.extend VMonad σ A) Ξ Γ
          ⟨$⟩ y)
          ∎
      where
        η-ˢ∘ᵛ : ∀ {Ξ} {Ψ} {Γ} {Δ} (ρ : Γ ⇒ᵛ Δ) (ι : Ξ ⇒ᵐ Ψ)
               → (λ {B} → _⟨$⟩_ (η (σ B) Θ Δ)) ˢ∘ᵛ (ʳ⇑ᵛ ρ)
                 ≈ˢ ʳ⇑ᵛ ρ ᵛ∘ˢ (λ {B} x₁ → η (σ B) Θ Γ ⟨$⟩ x₁)
        η-ˢ∘ᵛ {Γ = Γ′} {Δ′} ρ ι (var-inl x) =
                   begin⟨ Term-setoid Θ _ _ ⟩
                     ((λ {B} → _⟨$⟩_ (η (σ B) Θ _)) ˢ∘ᵛ (ʳ⇑ᵛ ρ)) (var-inl x) ≈⟨ {!!} ⟩
                     {!!} ≈⟨ {!!} ⟩
                     {!!} ≈⟨ {! ˢ∘ᵛ-η (σ A₁) Θ Γ₁η (σ A₁) Θ Γ₁ᵛ∘ˢ-disjoint ˢ∘ᵛ-ᵛ∘uˢ-disjoint!} ⟩
                     (ʳ⇑ᵛ ρ ᵛ∘ˢ (λ {B} → _⟨$⟩_ (η (σ B) Θ _))) (var-inl x) ∎
               where
                 ˢ∘ᵛ-ᵛ∘ˢ-disjoint : ∀ {ψ} {Γ Ξ Δ Λ} (σ : ψ ⊕ Ξ ⇒ˢ Λ) (ρ : Γ ⇒ᵛ Δ)
                                      →  ⇑ˢ σ ˢ∘ᵛ ʳ⇑ᵛ ρ  ≈ˢ ʳ⇑ᵛ ρ ᵛ∘ˢ ⇑ˢ σ
                 ˢ∘ᵛ-ᵛ∘ˢ-disjoint σ τ (var-inl x) =
                                        begin⟨ Term-setoid _ _ _ ⟩
                                          ([ var-inl ]ᵛ σ x) ≈⟨ []ᵛ-resp-≡ᵛ (λ x₃ → refl) ⟩
                                          ([ [ (λ x₃ → var-inl x₃) , (λ x₃ → var-inr (τ x₃)) ]ᵛ ∘ᵛ var-inl ]ᵛ σ x) ≈⟨ [∘ᵛ] ⟩
                                          ([ [ (λ x₃ → var-inl x₃) , (λ x₃ → var-inr (τ x₃)) ]ᵛ ]ᵛ ([ var-inl ]ᵛ σ x)) ∎
                 ˢ∘ᵛ-ᵛ∘ˢ-disjoint σ τ (var-inr x) = ≈-refl
        η-ˢ∘ᵛ ρ ι (var-inr x) = {!!}
    Monad.identityʳ VMonad {_} {_} {𝒩s} =
                           λ i {k = Ω} {Γ = Γ} {x = x} {y = y} x≈y
                             → begin⟨ Term-setoid Θ _ _ ⟩
                                      (η (𝒩s i) Θ Γ ⟨$⟩ x) ≈⟨ {!!} ⟩
                                      (η (𝒩s i) Ω Γ ⟨$⟩ x) ≈⟨  (func-cong (η (𝒩s i) Ω Γ) (x≈y)) ⟩
                                      (η (𝒩s i) Ω Γ ⟨$⟩ y) ∎

    Monad.identityˡ VMonad = λ i x≈y →  ≈-trans [idˢ] x≈y
    Monad.assoc VMonad  {Γ} {Δ} {Ξ} {k} {l} = λ A {ψ} {Λ} {x} {y} ξ
                         → begin⟨ Term-setoid Θ _ _ ⟩
                             ([ (λ {B} x₁ → [ (λ {B = B₁} → _⟨$⟩_ (η (l B₁) Θ Λ)) ]ˢ (η (k B) Θ Λ ⟨$⟩ x₁)) ]ˢ x)
                                ≈⟨ []ˢ-resp-≈ (λ {B} x₁ → [ (λ {B = B₁} → _⟨$⟩_ (η (l B₁) Θ Λ)) ]ˢ (η (k B) Θ Λ ⟨$⟩ x₁)) ξ ⟩
                             ([ (λ {B} x₁ → [ (λ {B = B₁} → _⟨$⟩_ (η (l B₁) Θ Λ)) ]ˢ (η (k B) Θ Λ ⟨$⟩ x₁)) ]ˢ y) ≈⟨ [∘ˢ] y ⟩
                             ([ (λ {B} → _⟨$⟩_ (η (l B) Θ Λ)) ]ˢ ([ (λ {B} → _⟨$⟩_ (η (k B) Θ Λ)) ]ˢ y)) ∎
    Monad.extend-≈ VMonad {Γ} {Δ} {k} {h} = λ ξ A {ψ} {Λ} {t} {u} ξᵗ
                                            → begin⟨ Term-setoid Θ _ _ ⟩
                                              ([ (λ {B} → _⟨$⟩_ (η (k B) Θ Λ)) ]ˢ t) ≈⟨ []ˢ-resp-≈ (λ {B} → _⟨$⟩_ (η (k B) Θ Λ)) ξᵗ ⟩
                                              ([ (λ {B} → _⟨$⟩_ (η (k B) Θ Λ)) ]ˢ u) ≈⟨ []ˢ-resp-≈ˢ u (λ {A = C} x → ξ C refl) ⟩
                                              ([ (λ {B} → _⟨$⟩_ (η (h B) Θ Λ)) ]ˢ u) ∎



















-- *************************************************************************************


-- open import Agda.Primitive using (lzero; lsuc; _⊔_ ;Level)
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; setoid; cong; trans)
-- import Function.Equality
-- open import Relation.Binary using (Setoid)

-- import Categories.Category
-- import Categories.Functor
-- import Categories.Category.Instance.Setoids
-- import Categories.Monad.Relative
-- import Categories.Category.Equivalence
-- import Categories.Category.Cocartesian
-- import Categories.Category.Construction.Functors
-- import Categories.NaturalTransformation.Equivalence
-- import Relation.Binary.Core

-- import SecondOrder.Arity
-- import SecondOrder.Signature
-- import SecondOrder.Metavariable
-- import SecondOrder.VRenaming
-- import SecondOrder.MRenaming
-- import SecondOrder.Term
-- import SecondOrder.IndexedCategory
-- import SecondOrder.RelativeKleisli
-- import SecondOrder.Substitution

-- module SecondOrder.VRelMon
--   {ℓ}
--   {𝔸 : SecondOrder.Arity.Arity}
--   (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
--   where

--   open SecondOrder.Signature.Signature Σ
--   open SecondOrder.Metavariable Σ
--   open SecondOrder.Term Σ
--   open SecondOrder.VRenaming Σ
--   open SecondOrder.MRenaming Σ
--   open SecondOrder.Substitution Σ


--   -- TERMS FORM A RELATIVE MONAD
--   -- (FOR A FUNCTOR WHOSE DOMAIN IS THE
--   -- CATEGORY OF VARIABLE CONTEXTS AND RENAMINGS)

--   module _ where
--     open Categories.Category
--     open Categories.Functor using (Functor)
--     open Categories.Category.Instance.Setoids
--     open Categories.Monad.Relative
--     open Function.Equality using () renaming (setoid to Π-setoid)
--     open Categories.Category.Equivalence using (StrongEquivalence)
--     open import SecondOrder.IndexedCategory
--     open import SecondOrder.RelativeKleisli
--     open Categories.Category.Construction.Functors
--     open Categories.NaturalTransformation.Equivalence
--     open Relation.Binary.Core hiding (_⇒_)

--     -- The carrier of the codomain of Jⱽ (morally ∀ Γ → A ∈ Δ ,, Γ)
--     record Codomain-Jⱽ-Elt : Set ((lsuc ℓ)) where
--       open Category (Setoids ℓ ℓ)
--       open Setoid
--       field
--         F₀ :  VContext → MContext → Obj
--         F₁ : ∀ {Θ ψ Δ Ξ} (ρ : Δ ⇒ᵛ Ξ) (ι : Θ ⇒ᵐ ψ)
--              → (F₀ Δ Θ) ⇒ (F₀ Ξ ψ)
--         identity : ∀ {Θ Δ}
--                    → Category._≈_ (Setoids ℓ ℓ) (F₁ (idᵛ {Δ}) (idᵐ {Θ})) (id {F₀ Δ Θ})
--         homomorphism : ∀ {Θ ψ Ω Γ Δ Ξ} {ρ : Γ ⇒ᵛ Δ} {ι : Θ ⇒ᵐ ψ} {τ : Δ ⇒ᵛ Ξ} {μ : ψ ⇒ᵐ Ω}
--                        → Category._≈_ (Setoids ℓ ℓ) (F₁ (τ ∘ᵛ ρ) (μ ∘ᵐ ι)) ((F₁ τ μ) ∘ (F₁ ρ ι))
--         F-resp-≈ : ∀ {Θ ψ Γ Δ} {ρ τ : Γ ⇒ᵛ Δ} {ι μ : Θ ⇒ᵐ ψ}
--                    → (ρ ≡ᵛ τ) → (ι ≡ᵐ μ) → (Category._≈_ (Setoids ℓ ℓ) (F₁ ρ ι) (F₁ τ μ))



--     -- Transformation for Codomain-Jⱽ (analogue to natural transformations)

--     record NaturalTransformation-Jⱽ (Fⱽ Gⱽ : Codomain-Jⱽ-Elt) : Set (lsuc ℓ)
--       where
--         private
--           module Fⱽ = Codomain-Jⱽ-Elt Fⱽ
--           module Gⱽ = Codomain-Jⱽ-Elt Gⱽ
--         open Fⱽ using (F₀; F₁)
--         open Category (Setoids ℓ ℓ)
--         field
--           η : ∀ Θ Γ → (F₀ Γ Θ) ⇒ (Gⱽ.F₀ Γ Θ)
--           commute : ∀ {Θ ψ Γ Δ} (ρ : Γ ⇒ᵛ Δ) (ι : Θ ⇒ᵐ ψ)
--                     → Category._≈_ (Setoids ℓ ℓ) ((η ψ Δ) ∘ (F₁ ρ ι)) ((Gⱽ.F₁ ρ ι) ∘ (η Θ Γ))

--     open NaturalTransformation-Jⱽ



--     -- Equivalence of NaturalTransformation-Jⱽ (analogue to the one
--     -- of the natural transformations)

--     infix 4 _≃Jⱽ_

--     _≃Jⱽ_ : ∀ {Fⱽ Gⱽ : Codomain-Jⱽ-Elt} → Rel (NaturalTransformation-Jⱽ Fⱽ Gⱽ) ℓ
--     𝒩 ≃Jⱽ ℳ  = ∀ {Θ Γ} → Category._≈_ (Setoids ℓ ℓ)
--                             (η 𝒩 Θ Γ)
--                             (η ℳ Θ Γ)


--     -- Identity transformation analogue to the one
--     -- of the natural transformations, for NaturalTransformation-Jⱽ

--     idN-Jⱽ : ∀ {Fⱽ : Codomain-Jⱽ-Elt} → NaturalTransformation-Jⱽ Fⱽ Fⱽ
--     idN-Jⱽ {Fⱽ} =
--            record
--              { η = λ Θ Γ →
--                record
--                  { _⟨$⟩_ = λ x → x
--                  ; cong = λ x → x }
--              ; commute = λ {Θ} {ψ} {Γ} {Δ} ρ ι ξ
--                          → Codomain-Jⱽ-Elt.F-resp-≈  Fⱽ {Θ} {ψ} {Γ} {Δ} {ρ} {ρ} {ι} {ι}
--                                                 (λ x₁ → refl) (λ M → refl) ξ }




--     -- Composition of NaturalTransformation-Jⱽ (analogue to the one
--     -- of the natural transformations)

--     _∘-Jⱽ_ : ∀ {Fⱽ Gⱽ Hⱽ : Codomain-Jⱽ-Elt} (𝒩 : NaturalTransformation-Jⱽ Gⱽ Hⱽ) (ℳ : NaturalTransformation-Jⱽ Fⱽ Gⱽ) → NaturalTransformation-Jⱽ Fⱽ Hⱽ
--     _∘-Jⱽ_ {Fⱽ} {Gⱽ} {Hⱽ} 𝒩 ℳ =
--              let open Category (Setoids ℓ ℓ) in
--              let open NaturalTransformation-Jⱽ in
--              let open Codomain-Jⱽ-Elt in
--              record
--                  { η = λ Θ Γ → η 𝒩 Θ Γ ∘ η ℳ Θ Γ
--                  ; commute = λ {Θ} {ψ} {Γ} {Δ} ρ ι →
--                              let open HomReasoning {F₀ Fⱽ Γ Θ} {F₀ Hⱽ Δ ψ} in
--                              begin
--                              (Category._∘_ (Setoids ℓ ℓ) (η {Gⱽ} {Hⱽ} 𝒩 ψ Δ) ((η {Fⱽ} {Gⱽ} ℳ ψ Δ) ∘ (F₁ Fⱽ ρ ι))) ≈⟨ assoc {f = F₁ Fⱽ ρ ι} {g = η ℳ ψ Δ} {h = η 𝒩 ψ Δ} ⟩
--                              (η 𝒩 ψ Δ ∘ (η ℳ ψ Δ) ∘ (F₁ Fⱽ ρ ι)) ≈⟨ refl⟩∘⟨_
--                                                                       {f = η 𝒩 ψ Δ} {g = (η ℳ ψ Δ) ∘ (F₁ Fⱽ ρ ι)}
--                                                                       {i = (F₁ Gⱽ ρ ι) ∘ (η ℳ Θ Γ)}
--                                                                       (commute ℳ ρ ι) ⟩
--                              (η 𝒩 ψ Δ ∘ ((F₁ Gⱽ ρ ι) ∘ (η ℳ Θ Γ))) ≈⟨ sym-assoc {f = η ℳ Θ Γ} {g = F₁ Gⱽ ρ ι} {h = η 𝒩 ψ Δ}⟩
--                              ((η 𝒩 ψ Δ) ∘ (F₁ Gⱽ ρ ι)) ∘ (η ℳ Θ Γ) ≈⟨ _⟩∘⟨refl
--                                                                       {f = (η 𝒩 ψ Δ) ∘ (F₁ Gⱽ ρ ι)} {h = (F₁ Hⱽ ρ ι) ∘ (η 𝒩 Θ Γ)}
--                                                                       {g = η ℳ Θ Γ}
--                                                                       (commute 𝒩 ρ ι) ⟩
--                              (((F₁ Hⱽ ρ ι) ∘ (η 𝒩 Θ Γ)) ∘ (η ℳ Θ Γ)) ≈⟨ assoc {f = η ℳ Θ Γ} {g = η 𝒩 Θ Γ} {h = F₁ Hⱽ ρ ι} ⟩
--                              (((F₁ Hⱽ ρ ι) ∘ (η 𝒩 Θ Γ)) ∘ (η ℳ Θ Γ)) ∎}



--     -- Proof that the category of Codomain-Jⱽ and NaturalTransformation-Jⱽ is indeed a category

--     -- associativity of composition
--     -- (surprisingly enough, the proof of "sym-assoc-Jⱽ" is exactly the same :
--     -- Is there a problem in the definitions ?)
--     assoc-Jⱽ : {A B C D : Codomain-Jⱽ-Elt}
--                {ℒ : NaturalTransformation-Jⱽ A B}
--                {ℳ : NaturalTransformation-Jⱽ B C}
--                {𝒩 : NaturalTransformation-Jⱽ C D}
--                → ((𝒩 ∘-Jⱽ ℳ) ∘-Jⱽ ℒ) ≃Jⱽ (𝒩 ∘-Jⱽ (ℳ ∘-Jⱽ ℒ))
--     assoc-Jⱽ  {A} {B} {C} {D} {ℒ} {ℳ} {𝒩} {Θ} {Γ} ξ = Function.Equality.Π.cong (η 𝒩 Θ Γ)
--                                                           (Function.Equality.Π.cong (η ℳ Θ Γ)
--                                                             (Function.Equality.cong (η ℒ Θ Γ) ξ))

--     -- identity is identity
--     identityˡ-Jⱽ : {A B : Codomain-Jⱽ-Elt}
--                   {𝒩 : NaturalTransformation-Jⱽ A B}
--                   → (idN-Jⱽ ∘-Jⱽ 𝒩) ≃Jⱽ 𝒩
--     identityˡ-Jⱽ  {𝒩 = 𝒩} {Θ = Θ} {Γ = Γ} ξ = Function.Equality.cong (η 𝒩 Θ Γ) ξ


--     -- Codomain of Jⱽ (the category with Codomain-Jⱽ-Elt as objects and NaturalTransformation-Jⱽ as maps)
--     Codomain-Jⱽ : Category (lsuc ℓ) (lsuc ℓ)  ℓ
--     Codomain-Jⱽ = record
--                     { Obj = Codomain-Jⱽ-Elt
--                     ; _⇒_ = NaturalTransformation-Jⱽ
--                     ; _≈_ = _≃Jⱽ_
--                     ; id = idN-Jⱽ
--                     ; _∘_ = _∘-Jⱽ_
--                     ; assoc = λ {Fⱽ} {Gⱽ} {Hⱽ} {Kⱽ} {𝒩} {ℳ} {ℒ} → assoc-Jⱽ  {ℒ = 𝒩} {ℳ = ℳ} {𝒩 = ℒ}
--                     ; sym-assoc = λ {Fⱽ} {Gⱽ} {Hⱽ} {Kⱽ} {𝒩} {ℳ} {ℒ} → assoc-Jⱽ  {ℒ = 𝒩} {ℳ = ℳ} {𝒩 = ℒ}
--                     ; identityˡ = λ {Fⱽ} {Gⱽ} {𝒩} → identityˡ-Jⱽ {𝒩 = 𝒩}
--                     ; identityʳ = λ {Fⱽ} {Gⱽ} {𝒩} → identityˡ-Jⱽ {𝒩 = 𝒩}
--                     ; identity² = λ {Fⱽ} ξ → ξ
--                     ; equiv = λ {Fⱽ} {Gⱽ}
--                               → record
--                                   { refl = λ {𝒩 = 𝒩} {Θ = Θ} {Γ = Γ} {x} {y} ξ
--                                            → Function.Equality.cong (η 𝒩 Θ Γ) ξ
--                                   ; sym = λ {𝒩} {ℳ} ξᴺ {Θ} {Γ} ξ
--                                           → Category.Equiv.sym (Setoids ℓ ℓ)
--                                           {_} {_} {η 𝒩 Θ Γ} {η ℳ Θ Γ} ξᴺ ξ
--                                   ; trans =  λ {𝒩} {ℳ} {ℒ} ξᴺ₂ ξᴺ₁ {Θ} {Γ} ξ
--                                              → Category.Equiv.trans (Setoids ℓ ℓ)
--                                              {_} {_} {η 𝒩 Θ Γ} {η ℳ Θ Γ} {η ℒ Θ Γ} ξᴺ₂ ξᴺ₁ ξ}
--                     ; ∘-resp-≈ = λ {Fⱽ} {Gⱽ} {Hⱽ} {𝒩} {ℳ} {ℒ} {𝒦} ξᴺ₁ ξᴺ₂ {Θ} {Γ} ξ
--                                  → Category.∘-resp-≈ (Setoids ℓ ℓ)
--                                    {_} {_}  {_}
--                                    {η 𝒩 Θ Γ} {η ℳ Θ Γ} {η ℒ Θ Γ} {η 𝒦 Θ Γ}
--                                    ξᴺ₁ ξᴺ₂ ξ
--                     }



--     -- The embedding of contexts into setoids indexed by sorts, metavariable telescope and variable telescope

--     Jⱽ : Functor VContexts (IndexedCategory sort Codomain-Jⱽ)
--     Jⱽ = record
--               { F₀ = λ Γ A →
--                        record
--                          { F₀ = λ Δ Θ → setoid (A ∈ (Γ ,, Δ))
--                          ; F₁ = λ ρ ι → record
--                                             { _⟨$⟩_ = [ inlᵛ , inrᵛ ∘ᵛ ρ ]ᵛ
--                                             ; cong = λ {x} {y} ξ →  ρ-resp-≡ {ρ = [ var-inl , var-inr ∘ᵛ ρ ]ᵛ} ξ}
--                          ; identity = λ {Θ} {Δ} {x} ξ → trans (idᵛ+idᵛ x) ξ
--                          ; homomorphism = λ {Θ} {ψ} {Ω} {Δ} {Ξ} {Λ} {ρ} {ι} {τ} {μ} {x} {y} ξ
--                                           → trans
--                                             (ʳ⇑ᵛ-resp-∘ᵛ x)
--                                             (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ}
--                                               (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (ρ x₁)) ]ᵛ} ξ))
--                          ; F-resp-≈ = λ {Θ} {ψ} {Δ} {Ξ} {ρ} {τ} {ι} {μ} ξᵛ ξᵐ {x} {y} ξ
--                                       → trans
--                                         ([,]ᵛ-resp-≡ᵛ (λ x₁ → refl) (∘ᵛ-resp-≡ᵛ {τ₁ = λ x₁ → var-inr x₁} (λ x₁ → refl) λ x₁ → ξᵛ x₁) x)
--                                         (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ} ξ)
--                          }

--               ; F₁ = λ ρ A → record
--                                { η = λ Θ Γ → record { _⟨$⟩_ = ⇑ᵛ ρ ; cong = cong (⇑ᵛ ρ) }
--                                ; commute = λ τ ι {x} ξ
--                                            → trans
--                                              (uniqueᵛ²
--                                                {τ = [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ ∘ᵛ [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ}
--                                                {σ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ ∘ᵛ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ} (λ x₁ → refl) (λ x₁ → refl) x)
--                                                (ρ-resp-≡
--                                                  {ρ = [ var-inl , (λ x₁ → var-inr (τ x₁)) ]ᵛ ∘ᵛ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ} ξ)}

--               ; identity =  λ A {Θ} {Γ} {x} ξ → trans (idᵛ+idᵛ x) ξ
--               ; homomorphism = λ {Δ} {Ξ} {Λ} {ρ} {τ} A {_} {_} {x} ξ
--                                → trans
--                                  (uniqueᵛ²
--                                    {τ = [ (λ x₁ → var-inl (τ (ρ x₁))) , (λ x₁ → var-inr x₁) ]ᵛ}
--                                    {σ = [ (λ x₁ → var-inl (τ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ ∘ᵛ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ}
--                                    (λ x₁ → refl) (λ x₁ → refl) x)
--                                  (ρ-resp-≡
--                                    {ρ = [ (λ x₁ → var-inl (τ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ ∘ᵛ [ (λ x₁ → var-inl (ρ x₁)) , (λ x₁ → var-inr x₁) ]ᵛ } ξ)
--               ; F-resp-≈ = λ {_} {_} {ρ} {τ} ξρ A {_} {_} {x} {y} ξ
--                            → trans
--                              (([,]ᵛ-resp-≡ᵛ {ρ₁ = λ x₁ → var-inl (ρ x₁)} {τ₁ = var-inr} (λ x₁ → ∘ᵛ-resp-≡ᵛ {τ₁ = var-inl} (λ x₃ → refl) ξρ x₁) (λ x₁ → refl) x))
--                              (ρ-resp-≡ {ρ = ⇑ᵛ τ} ξ)
--               }


--   -- The relative monad over Jⱽ

--   module _ {Θ : MContext} where
--     open Categories.Category
--     open Categories.Functor using (Functor)
--     open Categories.Category.Instance.Setoids
--     open Categories.Monad.Relative
--     open Function.Equality using () renaming (setoid to Π-setoid)
--     open Categories.Category.Equivalence using (StrongEquivalence)
--     open import SecondOrder.IndexedCategory
--     open import SecondOrder.RelativeKleisli
--     open NaturalTransformation-Jⱽ

--     VMonad : Monad Jⱽ
--     VMonad =
--       let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
--       record
--         { F₀ = λ Γ A → record
--                          { F₀ = λ Δ ψ → Term-setoid Θ (Γ ,, Δ) A
--                          ; F₁ = λ ρ ι → record { _⟨$⟩_ = [_]ᵛ_ (ʳ⇑ᵛ ρ) ; cong = λ ξ → []ᵛ-resp-≈ ξ }
--                          ; identity = λ ξ → ≈-trans ([]ᵛ-resp-≡ᵛ idᵛ+idᵛ) (≈-trans [idᵛ] ξ)
--                          ; homomorphism = λ {_} {_} {_} {_} {_} {_} {ρ} {_} {τ} ξ
--                                           → ≈-trans
--                                           ([]ᵛ-resp-≈ ξ)
--                                           (≈-trans
--                                             ([]ᵛ-resp-≡ᵛ λ x₁
--                                               → uniqueᵛ²
--                                                 {τ = [ (λ x₂ → var-inl x₂) , (λ x₂ → var-inr (τ (ρ x₂))) ]ᵛ}
--                                                 {σ = [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (τ x₁)) ]ᵛ  ∘ᵛ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (ρ x₁)) ]ᵛ }
--                                                 (λ x₂ → refl) (λ x₂ → refl) x₁)
--                                             [∘ᵛ])

--                          ; F-resp-≈ = λ ξᵛ ξᵐ ξ → ≈-trans ([]ᵛ-resp-≈ ξ) ([]ᵛ-resp-≡ᵛ λ x → [,]ᵛ-resp-≡ᵛ (λ x₁ → refl) (λ x₁ → ρ-resp-≡ {ρ = var-inr} (ξᵛ x₁)) x )
--                          }
--         ; unit = λ A
--                    → record
--                      { η = λ ψ Γ
--                        → record
--                          { _⟨$⟩_ = λ x → tm-var x
--                          ; cong = λ ξ → congˢ-var {σ = tm-var} ξ }
--                        ; commute = λ ρ ι ξ → congˢ-var {σ = tm-var} (ρ-resp-≡ {ρ = [ var-inl , (λ x₁ → var-inr (ρ x₁)) ]ᵛ} ξ) }
--         ; extend = {!!}
--         ; identityʳ = λ A ξ → {!!}
--         ; identityˡ = {!!}
--         ; assoc = {!!}
--         ; extend-≈ = {!!}
--         }


--     -- Other possibility, if the above doesn't work :

--     -- Jⱽ′ : Functor VContexts (Functors MContexts (Functors VContexts (IndexedCategory sort (Setoids ℓ ℓ))))
--     -- Jⱽ′ = record
--     --           { F₀ = {!!} -- λ Γ A → setoid (A ∈ Γ)
--     --           ; F₁ = {!!} -- λ ρ A → record { _⟨$⟩_ = ρ ; cong = cong ρ }
--     --           ; identity = {!!} -- λ A ξ → ξ
--     --           ; homomorphism = {!!} -- λ {_} {_} {_} {ρ} {σ} A {_} {_} ξ → cong σ (cong ρ ξ)
--     --           ; F-resp-≈ = {!!} -- λ ξ A ζ → trans (ξ _) (cong _ ζ)
--     --           }
