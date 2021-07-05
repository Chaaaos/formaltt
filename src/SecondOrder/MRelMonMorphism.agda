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

  module MRelMonMorph {Γ Γ′ : VContext} where
    open MTerm {Γ} renaming (MMonad to M_Γ)
    open MTerm {Γ′} renaming (MMonad to M_Γ′)


    Fᴹ : ∀ (ρ : Γ ⇒ᵛ Γ′) →  RMonadMorph (M_Γ) (M_Γ′)
    Fᴹ ρ = record
            { morph = λ Γᴹ Aᴹ →
                        record
                          { _⟨$⟩_ = [ ⇑ᵛ ρ ]ᵛ_
                          ; cong =  λ M≈N → []ᵛ-resp-≈ M≈N
                          }
            ; law-unit =  λ Γᴹ Aᴹ M≡N → ≈-≡
                                          (I-resp-≡
                                            {I = λ M → tm-meta M λ i → tm-var (var-inr i) }
                                            M≡N)
            ; law-extend = λ {Θ} {Ω} {k} Γᴹ Aᴹ {s} {t} s≈t →
                                       ≈-trans
                                           ([ᵛ∘ⁱ] s)
                                           (≈-trans
                                             ([]ⁱ-resp-≈
                                               (⇑ᵛ ρ ᵛ∘ⁱ ⇑ⁱ (λ {Λ} {B} →
                                                   Function.Equality._⟨$⟩_ (k Λ B)))
                                               ([]ᵛ-resp-≈ s≈t))
                                             ([]ⁱ-resp-≈ⁱ ([ (⇑ᵛ ρ) ]ᵛ t) λ M →
                                               (≈-trans
                                                 (≈-sym [∘ᵛ])
                                                 (≈-trans
                                                   ([]ᵛ-resp-≡ᵛ extend-aux)
                                                   [∘ᵛ]))))
            }

           where
             extend-aux : ∀ {Ξ Λ} → ⇑ᵛ {Ξ = Ξ} (⇑ᵛ {Ξ = Λ} ρ) ∘ᵛ (⇑ᵛ var-inl) ≡ᵛ ⇑ᵛ var-inl ∘ᵛ (⇑ᵛ ρ)
             extend-aux (var-inl x) = refl
             extend-aux (var-inr x) = refl




















  -- Attempt with substitutions instead of renamings : not sure it works
    -- hat : (f : (Θ : MContext) → Θ ⊕ Γ ⇒ˢ Γ') → RMonadMorph M_Γ M_Γ'
    -- hat f =
    --   let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
    --   record
    --   { morph = λ {Θ} Δ A → record { _⟨$⟩_ = λ t → [ ⇑ˢ (f Θ) ]ˢ t ; cong = []ˢ-resp-≈ (⇑ˢ (f Θ))}
    --   ; law-unit = λ Δ A {t} {s} t≡s → ≈-≡ (cong tm-meta-generic t≡s)
    --   ; law-extend = λ {Θ} {Ψ} {I} Δ A {t} {s} t≈s →
    --       let open SetoidR (Term-setoid Ψ (Γ' ,, Δ) A) in
    --       begin
    --       ([ ⇑ˢ (f Ψ) ]ˢ ([ ⇑ⁱ (λ {Λ} {B} M →  (I Λ B ⟨$⟩ M) ) ]ⁱ t) )
    --         ≈⟨ {!!} ⟩ -- this is the crucial step
    --       ([ ⇑ⁱ (λ {Λ} {B} M → [ ⇑ˢ (f Ψ) ]ˢ (I Λ B ⟨$⟩ M)) ]ⁱ ([ ⇑ˢ (f Θ) ]ˢ t))
    --         ≈⟨ []ⁱ-resp-≈ (⇑ⁱ (λ {Λ} {B} M → [ ⇑ˢ (f Ψ) ]ˢ (I Λ B ⟨$⟩ M))) ([]ˢ-resp-≈ (⇑ˢ (f Θ)) t≈s) ⟩
    --       ([ ⇑ⁱ (λ {Λ} {B} M → [ ⇑ˢ (f Ψ) ]ˢ (I Λ B ⟨$⟩ M)) ]ⁱ ([ ⇑ˢ (f Θ) ]ˢ s))
    --       ∎
    --   }
