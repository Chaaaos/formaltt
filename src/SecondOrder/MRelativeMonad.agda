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


module SecondOrder.MRelativeMonad
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
  open import SecondOrder.RelativeMonadMorphism
  open Categories.Category
  open Categories.Functor using (Functor)
  open Categories.NaturalTransformation renaming (id to idNt)
  open Categories.NaturalTransformation.NaturalIsomorphism renaming (refl to reflNt; sym to symNt; trans to transNt)
  open Categories.Category.Construction.Functors
  open Categories.Category.Instance.Setoids
  open Categories.Category.Product
  open Function.Equality using () renaming (setoid to Π-setoid)
  open SecondOrder.IndexedCategory

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
        -- The object mapping (which is also a functor)
        { F₀ = λ Θ Δ A → Term-setoid Θ (Γ ,, Δ) A
        -- The unit of the relative monad
        ; unit = λ {Θ} Δ A →
               record
               { _⟨$⟩_ = λ M → tm-meta-generic M
               ; cong = λ {M} {N} M≡N → ≈-≡ (cong tm-meta-generic M≡N)
               }
        -- The extension in the rel monad
        ; extend = λ {Θ} {Ψ} I Δ A →
                 record
                 { _⟨$⟩_ = λ t → [ ⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M) ]ⁱ t
                 ; cong = λ {t} {s} t≈s →
                   let open SetoidR (Term-setoid Ψ (Γ ,, Δ) A) in
                   begin
                   ([ ⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M) ]ⁱ t)
                     ≈⟨ []ⁱ-resp-≈ (⇑ⁱ (λ {Λ} {B} → _⟨$⟩_ (I Λ B))) t≈s ⟩
                   ([ ⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M) ]ⁱ s)
                   ∎
                 }
        -- This is the law that says: I* ∘ η = I
        ; identityʳ = λ {Θ} {Ψ} {I} Δ A {t} {s} t≈s
            → ≈-trans ([]ⁱ-generic {Θ} {Ψ} {Γ} {λ {Λ} {B} M → I Λ B ⟨$⟩ M}) (func-cong (I Δ A) t≈s)
        -- This is the law that says η* = id
        ; identityˡ = λ {Θ} Δ A {t} {s} t≈s →
            let open SetoidR (Term-setoid Θ (Γ ,, Δ) A) in
            begin
            ([ ⇑ⁱ (λ {Λ} {B} M → tm-meta-generic M) ]ⁱ t) ≈⟨ []ⁱ-resp-≈ (⇑ⁱ tm-meta-generic) t≈s ⟩
            ([ ⇑ⁱ (λ {Λ} {B} M → tm-meta-generic M) ]ⁱ s) ≈⟨ [idⁱ] ⟩
            s
            ∎
        -- This is the law that says: (J* ∘ I)* = J* ∘ I*
        ; assoc = λ {Θ} {Ψ} {Ξ} {I} {J} Δ A {t} {s} t≈s →
            let open SetoidR (Term-setoid Ξ (Γ ,, Δ) A) in
            begin
            ([ ⇑ⁱ ((λ {Λ} {B} M → J Λ B ⟨$⟩ M) ∘ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M)) ]ⁱ t)
              ≈⟨ []ⁱ-resp-≈ⁱ t (⇑ⁱ-resp-∘ⁱ {Θ} {Ψ} {Ξ} {Γ} {Δ} {(λ {Λ} {B} M → I Λ B ⟨$⟩ M)}) ⟩
            ([ (⇑ⁱ (λ {Λ} {B} M → J Λ B ⟨$⟩ M)) ∘ⁱ (⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M)) ]ⁱ t)
              ≈⟨ [∘ⁱ] t ⟩
            ([ ⇑ⁱ (λ {Λ} {B} M → J Λ B ⟨$⟩ M) ]ⁱ ([ ⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M) ]ⁱ t))
              ≈⟨ []ⁱ-resp-≈ (⇑ⁱ (λ {Λ} {B} M → J Λ B ⟨$⟩ M))
                            ([]ⁱ-resp-≈ (⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M)) t≈s) ⟩
            ([ ⇑ⁱ (λ {Λ} {B} M → J Λ B ⟨$⟩ M) ]ⁱ ([ ⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M) ]ⁱ s))
            ∎
        -- Extension respects equality of instantiations
        ; extend-≈ = λ {Θ} {Ψ} {I} {J} I≈ⁱJ Δ A {t} {s} t≈s →
            let open SetoidR (Term-setoid Ψ (Γ ,, Δ) A) in
            begin
            ([ ⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M) ]ⁱ t) ≈⟨ []ⁱ-resp-≈ (⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M)) t≈s ⟩
            (([ ⇑ⁱ (λ {Λ} {B} M → I Λ B ⟨$⟩ M) ]ⁱ s))
              ≈⟨ []ⁱ-resp-≈ⁱ s (⇑ⁱ-resp-≈ⁱ ((λ {Λ} {B} M → I Λ B ⟨$⟩ M))
                ((λ {Λ} {B} M → J Λ B ⟨$⟩ M)) λ M → I≈ⁱJ _ _ refl) ⟩
            ([ ⇑ⁱ (λ {Λ} {B} M → J Λ B ⟨$⟩ M) ]ⁱ s)
            ∎
        }
