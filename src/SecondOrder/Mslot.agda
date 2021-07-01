{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; setoid)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; zip; map; <_,_>; swap)
import Function.Equality
-- open import Relation.Binary using (Setoid)
-- import Relation.Binary.Reasoning.Setoid as SetoidR

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
import SecondOrder.RelativeMonadMorphism
import SecondOrder.Instantiation
import SecondOrder.IndexedCategory
import SecondOrder.RelativeKleisli


module SecondOrder.Mslot
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.VRenaming Σ
  open SecondOrder.MRenaming Σ
  -- open SecondOrder.Substitution Σ
  -- open import SecondOrder.RelativeMonadMorphism
  -- open SecondOrder.Instantiation
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

  MTele = MContexts
  VTele = VContexts

  -- the codomain category of the MSlots functor. It should be equivalent to the
  -- functor category [ MTele x VTele , < Setoid >ₛₒᵣₜ ]
  -- objects are functors, which are really pairs of functions, one on objects
  -- one on morphisms
  -- morphisms in this category are natural transformations

  module _ where
    open Category
    open NaturalTransformation
    open Function.Equality renaming (_∘_ to _∙_)

  Mslots : Functor MContexts (IndexedCategory VContext (IndexedCategory sort (Setoids ℓ ℓ)))
  Mslots =  
    let open Categories.NaturalTransformation in
    let open NaturalTransformation in
    let open Relation.Binary.PropositionalEquality.≡-Reasoning in
      record
        { F₀ = λ Θ Γ A → setoid ([ Γ , A ]∈ Θ)
        ; F₁ = λ ι Γ A → record { _⟨$⟩_ = λ M → ι M ; cong = λ M≡N → cong ι M≡N }
        ; identity = λ {Θ} Γ A {M} {N} M≡N → cong idᵐ M≡N
        ; homomorphism = λ {Θ} {Ψ} {Ξ} {ι} {μ} Γ A M≡N → cong (μ ∘ᵐ ι) M≡N
        ; F-resp-≈ = λ {Θ} {Ψ} {ι} {μ} ι≡ᵐμ Γ A {M} {N} M≡N →
                   begin
                   ι M ≡⟨ cong ι M≡N ⟩
                   ι N ≡⟨ ι≡ᵐμ N ⟩
                   μ N
                   ∎
        }
