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
        F₀ :  VContext → MContext → Obj
        F₁ : ∀ {Θ ψ Δ Ξ} (ρ : Δ ⇒ᵛʳ Ξ) (ι : Θ ⇒ᵐʳ ψ)
             → (F₀ Δ Θ) ⇒ (F₀ Ξ ψ)
        identity : ∀ {Θ Δ}
                   → Category._≈_ (Setoids ℓ ℓ) (F₁ (idᵛʳ {Δ}) (idᵐʳ {Θ})) (id {F₀ Δ Θ})
        homomorphism : ∀ {Θ ψ Ω Γ Δ Ξ} {ρ : Γ ⇒ᵛʳ Δ} {ι : Θ ⇒ᵐʳ ψ} {τ : Δ ⇒ᵛʳ Ξ} {μ : ψ ⇒ᵐʳ Ω}
                       → Category._≈_ (Setoids ℓ ℓ) (F₁ (τ ∘ᵛʳ ρ) (μ ∘ᵐʳ ι)) ((F₁ τ μ) ∘ (F₁ ρ ι))
        F-resp-≈ : ∀ {Θ ψ Γ Δ} {ρ τ : Γ ⇒ᵛʳ Δ} {ι μ : Θ ⇒ᵐʳ ψ}
                   → (ρ ≡ᵛʳ τ) → (ι ≡ᵐʳ μ) → (Category._≈_ (Setoids ℓ ℓ) (F₁ ρ ι) (F₁ τ μ))

    -- definition of transformation analogue to natural transformations, for Functors-Jⱽ

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


    -- definition of an equivalence of transformation analogue to the one
    -- of the natural transformations, for NaturalTransformation-Jⱽ

    infix 4 _≃Jⱽ_

    _≃Jⱽ_ : ∀ {Fⱽ Gⱽ : Functor-Jⱽ} → Rel (NaturalTransformation-Jⱽ Fⱽ Gⱽ) ℓ
    𝒩 ≃Jⱽ ℳ  = ∀ {Θ Γ} → Category._≈_ (Setoids ℓ ℓ)
                            (NaturalTransformation-Jⱽ.η 𝒩 Θ Γ)
                            (NaturalTransformation-Jⱽ.η ℳ Θ Γ)


    -- definition of an identity transformation analogue to the one
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


    -- definition of the composition of transformations analogue to the one
    -- of the natural transformations, for NaturalTransformation-Jⱽ

    -- open import Function.Equality hiding (_∘_)
    -- open import Relation.Binary.Indexed.Heterogeneous.Bundles
    -- _≈⟨$⟩≈_ : ∀ {A : Setoid ℓ ℓ}
    --            {B : IndexedSetoid (Setoid.Carrier A) ℓ ℓ}
    --            {x y : Setoid.Carrier A}
    --            {f g : Π A B}
    --            → (∀ x → IndexedSetoid._≈_ B (f ⟨$⟩ x) (g ⟨$⟩ x)) → (Setoid._≈_ A x y) →  IndexedSetoid._≈_ B (g ⟨$⟩ y) (f ⟨$⟩ x)
    -- _≈⟨$⟩≈_ = {!!}

    _∘-Jⱽ_ : ∀ {Fⱽ Gⱽ Hⱽ : Functor-Jⱽ} (𝒩 : NaturalTransformation-Jⱽ Gⱽ Hⱽ) (ℳ : NaturalTransformation-Jⱽ Fⱽ Gⱽ) → NaturalTransformation-Jⱽ Fⱽ Hⱽ
    _∘-Jⱽ_ {Fⱽ} {Gⱽ} {Hⱽ} 𝒩 ℳ =
             let open Category (Setoids ℓ ℓ) in
             let open NaturalTransformation-Jⱽ in
             let open Functor-Jⱽ in
             record
                 { η = λ Θ Γ → η 𝒩 Θ Γ ∘ η ℳ Θ Γ
                 ; commute = λ {Θ} {ψ} {Γ} {Δ} ρ ι → {!!} }
-- Essentially, what I want to say is :
-- ((η 𝒩 ψ Δ ∘ η ℳ ψ Δ) ∘ (F₁ Fⱽ ρ ι)) =[assoc] (η 𝒩 ψ Δ ∘ (η ℳ ψ Δ) ∘ (F₁ Fⱽ ρ ι))
--                                       =[commute 𝒩] (η 𝒩 ψ Δ ∘ ((F₁ Gⱽ ρ ι) ∘ (η ℳ Θ Γ)))
--                                       =[sym-assoc] ((η 𝒩 ψ Δ ∘ (F₁ Gⱽ ρ ι)) ∘ (η ℳ Θ Γ))
--                                       =[commute ℳ] (((F₁ Hⱽ ρ ι) ∘ (η 𝒩 Θ Γ)) ∘ (η ℳ Θ Γ))
--                                       =[assoc] (((F₁ Hⱽ ρ ι) ∘ (η 𝒩 Θ Γ)) ∘ (η ℳ Θ Γ))
-- But it stops working at the first associativity step.
-- It looks like Agda doesn't understand what equality I want to use.
-- I tried to make it explicit, but didn't succeed.


    -- proof that the category of Functors-Jⱽ and NaturalTransformation-Jⱽ is indeed a category

    -- associativity NaturalTransformation-Jⱽ.η 𝒩 Θ Γ
    assoc-Jⱽ : {A B C D : Functor-Jⱽ}
               {ℒ : NaturalTransformation-Jⱽ A B}
               {ℳ : NaturalTransformation-Jⱽ B C}
               {𝒩 : NaturalTransformation-Jⱽ C D}
               → ((𝒩 ∘-Jⱽ ℳ) ∘-Jⱽ ℒ) ≃Jⱽ (𝒩 ∘-Jⱽ (ℳ ∘-Jⱽ ℒ))
    assoc-Jⱽ  {A} {B} {C} {D} {ℒ} {ℳ} {𝒩} {Θ} {Γ} = λ ξ → {!!}

    sym-assoc-Jⱽ : {A B C D : Functor-Jⱽ}
                {f : NaturalTransformation-Jⱽ A B}
                {g : NaturalTransformation-Jⱽ B C}
                {h : NaturalTransformation-Jⱽ C D}
                → (h ∘-Jⱽ (g ∘-Jⱽ f)) ≃Jⱽ ((h ∘-Jⱽ g) ∘-Jⱽ f)
    sym-assoc-Jⱽ = {!!}

    -- Codomain of Jⱽ (the category with Functor-Jⱽ as objects and NaturalTransformation-Jⱽ as maps)
    Functors-Jⱽ : Category (lsuc ℓ) (lsuc ℓ)  ℓ
    Functors-Jⱽ = record
                    { Obj = Functor-Jⱽ
                    ; _⇒_ = NaturalTransformation-Jⱽ
                    ; _≈_ = _≃Jⱽ_
                    ; id = idN-Jⱽ
                    ; _∘_ = _∘-Jⱽ_
                    ; assoc = {!assoc-Jⱽ!}
                    ; sym-assoc = {!sym-assoc-Jⱽ!}
                    ; identityˡ = {!!}
                    ; identityʳ = {!!}
                    ; identity² = {!!}
                    ; equiv = {!!}
                    ; ∘-resp-≈ = {!!}
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
                         ; identity = λ {x = x} {y = y} ξ → trans {![]ᵛʳ-resp!} {!!}
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
