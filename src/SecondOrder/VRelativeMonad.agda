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

module SecondOrder.VRelativeMonad
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
    open import SecondOrder.IndexedCategory

    -- The embedding of contexts into setoids indexed by sorts
    -- (seen as a "variable" functor)

    Jⱽ : Functor VContexts (IndexedCategory sort (Setoids ℓ ℓ))
    Jⱽ = slots

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
    open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong)
    open import Relation.Binary.Reasoning.MultiSetoid

    to-σ  : ∀ {Γ Δ} → (IndexedCategory sort (Setoids ℓ ℓ) Category.⇒ Functor.₀ Jⱽ Γ) (λ A → Term-setoid Θ Δ A) → (Θ ⊕ Γ ⇒ˢ Δ)
    to-σ ℱ {A} x = ℱ A ⟨$⟩ x

    VMonad : Monad Jⱽ
    VMonad = record
               { F₀ = λ Γ A → Term-setoid Θ Γ A
               ; unit = λ A →
                          record
                            { _⟨$⟩_ = λ x → tm-var x
                            ; cong = λ ξ → ≈-≡ (σ-resp-≡ {σ = tm-var} ξ) }
               ; extend = λ ℱ A →
                            record
                              { _⟨$⟩_ = [ to-σ ℱ ]ˢ_
                              ; cong = λ ξ → []ˢ-resp-≈ (λ {B} z → ℱ B ⟨$⟩ z) ξ }
               ; identityʳ = λ {Γ} {Δ} {ℱ} A {x} {y} ξ → func-cong (ℱ A) ξ
               ; identityˡ = λ A ξ → ≈-trans [idˢ] ξ
               ; assoc = λ {Γ} {Δ} {Ξ} {k} {l} A {x} {y} ξ →
                           begin⟨ Term-setoid Θ _ _ ⟩
                             ( ([ (λ {B} r → [ (λ {A = B} z → l B ⟨$⟩ z) ]ˢ (k B ⟨$⟩ r)) ]ˢ x) ) ≈⟨ []ˢ-resp-≈ ((λ {B} r → [ (λ {A = B} z → l B ⟨$⟩ z) ]ˢ (k B ⟨$⟩ r))) ξ ⟩
                             ([ (λ {B} r → [ (λ {A = A₁} z → l A₁ ⟨$⟩ z) ]ˢ (k B ⟨$⟩ r)) ]ˢ y) ≈⟨ [∘ˢ] y ⟩
                             (([ (λ {B} z → l B ⟨$⟩ z) ]ˢ ([ (λ {B} z → k B ⟨$⟩ z) ]ˢ y))) ∎
               ; extend-≈ = λ {Γ} {Δ} {k} {h} ξˢ A {x} {y} ξ →
                           begin⟨ Term-setoid Θ _ _ ⟩
                             ([ (λ {B} z → k B ⟨$⟩ z) ]ˢ x) ≈⟨ []ˢ-resp-≈ ((λ {B} z → k B ⟨$⟩ z)) ξ ⟩
                             ([ (λ {B} z → k B ⟨$⟩ z) ]ˢ y) ≈⟨ []ˢ-resp-≈ˢ y (λ {B} z → ξˢ B refl) ⟩
                             ([ (λ {B} z → h B ⟨$⟩ z) ]ˢ y) ∎
               }
