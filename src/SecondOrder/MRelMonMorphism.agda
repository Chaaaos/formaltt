open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; setoid)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; zip; map; <_,_>; swap)
import Function.Equality
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

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


module SecondOrder.MRelMonMorphism
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
  open SecondOrder.MRelativeMonad Σ
  open SecondOrder.VRelativeMonad Σ
  open SecondOrder.RelativeMonadMorphism

  module MRelMonMorph {Γ Γ' : VContext} where
    open MTerm {Γ} renaming (MMonad to M_Γ)
    open MTerm {Γ'} renaming (MMonad to M_Γ')

    hat : (f : (Θ : MContext) → Θ ⊕ Γ ⇒ˢ Γ') → RMonadMorph M_Γ M_Γ'
    hat f =
      let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
      record
      { morph = λ {Θ} Δ A → record { _⟨$⟩_ = λ t → [ ⇑ˢ (f Θ) ]ˢ t ; cong = []ˢ-resp-≈ (⇑ˢ (f Θ))}
      ; law-unit = λ Δ A {t} {s} t≡s → ≈-≡ (cong tm-meta-generic t≡s)
      ; law-extend = λ {Θ} {Ψ} {I} Δ A {t} {s} t≈s →
          let open SetoidR (Term-setoid Ψ (Γ' ,, Δ) A) in
          begin
          ([ ⇑ˢ (f Ψ) ]ˢ ([ ⇑ⁱ (λ {Λ} {B} M →  (I Λ B ⟨$⟩ M) ) ]ⁱ t) )
            ≈⟨ {!!} ⟩ -- this is the crucial step
          ([ ⇑ⁱ (λ {Λ} {B} M → [ ⇑ˢ (f Ψ) ]ˢ (I Λ B ⟨$⟩ M)) ]ⁱ ([ ⇑ˢ (f Θ) ]ˢ t))
            ≈⟨ []ⁱ-resp-≈ (⇑ⁱ (λ {Λ} {B} M → [ ⇑ˢ (f Ψ) ]ˢ (I Λ B ⟨$⟩ M))) ([]ˢ-resp-≈ (⇑ˢ (f Θ)) t≈s) ⟩
          ([ ⇑ⁱ (λ {Λ} {B} M → [ ⇑ˢ (f Ψ) ]ˢ (I Λ B ⟨$⟩ M)) ]ⁱ ([ ⇑ˢ (f Θ) ]ˢ s))
          ∎
      }
  
