open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; setoid)
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
import SecondOrder.RelativeMonadMorphism
import SecondOrder.Instantiation
import SecondOrder.IndexedCategory
import SecondOrder.RelativeKleisli
import SecondOrder.Mslot
import SecondOrder.MRelativeMonad
import SecondOrder.VRelativeMonad

module SecondOrder.VRelMonMorphism
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.RelativeMonadMorphism
  open SecondOrder.Metavariable Σ
  open SecondOrder.VRelativeMonad Σ
  open SecondOrder.Instantiation Σ
  open SecondOrder.MRenaming Σ
  open SecondOrder.VRenaming Σ
  open SecondOrder.Term Σ
  open SecondOrder.Substitution Σ


  -- In this file, the goal is to show that given two variable relative monads
  -- on different metacontexts, metarenaming from one of the metacontexts to the other
  -- we can define a relative monad morphism between the two variable relative monads

  Fⱽ : ∀ (Θ Θ′ : MContext) (μ : Θ ⇒ᵐ Θ′) →  RMonadMorph (VMonad {Θ}) (VMonad {Θ′})
  Fⱽ Θ Θ′ μ = record
            { morph = λ A →
                        record
                          { _⟨$⟩_ = [ μ ]ᵐ_
                          ; cong = λ s≈t → []ᵐ-resp-≈ s≈t
                          }
            ; law-unit = λ A x≡y → ≈-≡ (σ-resp-≡ {σ = tm-var} x≡y)
            ; law-extend = λ {Γ} {Δ} {k} A {s} {t} s≈t →
                                           ≈-trans
                                             (≈-sym ([ᵐ∘ˢ] s))
                                             (≈-trans
                                               ([]ˢ-resp-≈ˢ ([ μ ]ᵐ s)   λ x → ≈-refl  )
                                               ([]ˢ-resp-≈ (λ {B} x → [ μ ]ᵐ (k B Function.Equality.⟨$⟩ x)) ([]ᵐ-resp-≈ s≈t)))
            }
