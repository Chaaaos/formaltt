{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc; _⊔_; Level)
open import Relation.Unary hiding (_∈_)
open import Data.Empty.Polymorphic
open import Data.List
open import Function.Base
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import SecondOrder.Arity

import SecondOrder.Substitution
import SecondOrder.SecondOrderSignature as SecondOrderSignature
import SecondOrder.SecondOrderTheory as SecondOrderTheory
import SecondOrder.MetaTheoremR as MetaTheoremR

module SecondOrder.MetaTheoremS {ℓ ℓs ℓo ℓa : Level}
                               {𝔸 : Arity}
                               {Σ : SecondOrderSignature.Signature {ℓs} {ℓo} {ℓa} 𝔸}
                               {T : SecondOrderTheory.Theory {ℓs} {ℓo} {ℓa} {𝔸} {Σ} ℓ} where

  open SecondOrderSignature {ℓs} {ℓo} {ℓa} 𝔸
  open Signature Σ
  open SecondOrder.Substitution {ℓs} {ℓo} {ℓa} {𝔸} {Σ}
  open SecondOrderTheory {ℓs} {ℓo} {ℓa} {𝔸} {Σ}
  open Theory {ℓ} T
  open MetaTheoremR



-- The following theorems are mostly interdependant, so the way we declare them is a bit different

  --===================================================================================================
  --∥                                    ====================                                         ∥
  --∥                                    ∥  ** Theorems **  ∥                                         ∥
  --∥                                    ====================                                         ∥
  --===================================================================================================

  --===================================================================================================


  ---------------------------------------------------------------------------------------------
  --=================================
  -- I. Renamings to substitutions ∥
  --=================================

  -- enables to use a renaming as a substitution
  r-to-subst : ∀ {Θ Γ Δ} (ρ : Θ ⊕ Γ ⇒ʳ Δ) → Θ ⊕ Δ ⇒ˢ Γ

  syntax r-to-subst ρ = ρ ˢ

  r-to-subst-⇑ˢ : ∀ {Θ Γ Δ Ξ} {ρ : Θ ⊕ Γ ⇒ʳ Δ}
    →  _≈ˢ_ {Θ = Θ} (r-to-subst (extendʳ {Θ = Θ} ρ {Ξ = Ξ})) (⇑ˢ (r-to-subst ρ))

  -- For any renaming ρ and term t, it doesn't matter if we act on t with
  -- the renaming ρ or act on t with the substitution induced by ρ
  -- Proposition 3.19 (1)
  r-to-subst-≈ :  ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {ρ : Θ ⊕ Γ ⇒ʳ Δ}
    → ⊢ Θ ⊕ Δ ∥ ([ ρ ]ʳ t) ≈ t [ r-to-subst ρ ]ˢ ⦂ A

  -- applying an extended renaming (ρ ⊕ Ξ) on a term t is the same as extending the
  -- substitution induced by the renaming ρ
  r-to-subst-≈aux : ∀ {Θ Γ Δ Ξ A} {t : Term Θ (Γ ,, Ξ) A} {ρ : Θ ⊕ Γ ⇒ʳ Δ}
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ ([(extendʳ {Θ = Θ} ρ)]ʳ t) ≈ t [ ⇑ˢ (r-to-subst ρ) ]ˢ ⦂ A

  ---------------------------------------------------------------------------------------------
  --=====================
  -- II. Substitutions ∥
  --=====================

  ---------------------
  -- A. Main theorems |
  ---------------------

  -- actions of equal substitutions are pointwise equal
  subst-congr : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Θ ⊕ Δ ⇒ˢ Γ}
    → σ ≈ˢ τ → ⊢ Θ ⊕ Δ ∥ t [ σ ]ˢ ≈  t [ τ ]ˢ ⦂ A

  -- action of the identity substitution is the identity
  -- Proposition 3.19 (2)
  id-action : ∀ {Θ Γ A} {a : Term Θ Γ A}
    → (⊢ Θ ⊕ Γ ∥ a ≈ (a [ idˢ ]ˢ) ⦂ A)

  -- substitution preserves equality of terms
  ≈tm-subst : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {σ : Θ ⊕ Δ ⇒ˢ Γ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Δ ∥ s [ σ ]ˢ ≈  t [ σ ]ˢ ⦂ A

  -- action of substitutions "commutes" with composition, i.e. is functorial
  -- Proposition 3.19 (4)
  ∘ˢ-≈ :  ∀ {Θ Γ Δ Ξ A} {t : Term Θ Γ A} {σ : Θ ⊕ Δ ⇒ˢ Γ} {τ : Θ ⊕ Ξ ⇒ˢ Δ}
    → ⊢ Θ ⊕ Ξ ∥ (t [ σ ]ˢ) [ τ ]ˢ ≈ (t [ σ ∘ˢ τ ]ˢ) ⦂ A

  --------------
  -- B. Lemmas |
  --------------

  -- extension of the identity substitution is the identity substitution
  idˢ-extendˡ : ∀ {Θ Γ Ξ A} {a : A ∈ (Γ ,, Ξ)}
    → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ ⇑ˢ {Θ} {Γ} {Γ} {Ξ} (idˢ {Γ = Γ}) {A} a ≈  idˢ {Γ = Γ ,, Ξ} a ⦂ A

  subst-congr-aux : ∀ {Θ Γ Δ Ξ A} {t : Term Θ (Γ ,, Ξ) A} {σ τ : Θ ⊕ Δ ⇒ˢ Γ}
    → σ ≈ˢ τ → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ t [ ⇑ˢ σ ]ˢ ≈  t [ ⇑ˢ τ ]ˢ ⦂ A

  -- interactions between extensions
  extend-var-inl : ∀ {Γ Δ Ξ Λ Θ A} (t : Term Θ (Λ ,, Ξ) A) (τ : Θ ⊕ Γ ⇒s Λ)
    → ⊢ Θ ⊕ ((Γ ,, Δ) ,, Ξ) ∥
        (([ (extend-r {Θ = Θ} var-inl) ]r t) [ extend-sˡ (extend-sˡ τ) ]s)
      ≈ ([ (extend-r {Θ = Θ} var-inl) ]r (t [ extend-sˡ τ ]s)) ⦂ A
  extend-var-inl {Γ} {Δ} {Ξ} {Λ} {Θ} {A} (tm-var (var-inl x)) τ =
    let open SetoidR (eq-setoid (Γ ,, Δ ,, Ξ) Θ A) in
      {!!}
  extend-var-inl (tm-var (var-inr y)) τ = {!!}
  extend-var-inl (tm-meta M ts) τ = {!!}
  extend-var-inl (tm-oper f es) τ = {!!}

  -- extension of substitutions preserve composition
  ∘s-extendˡ : ∀ {Θ Γ Δ Ξ Λ} {σ : Θ ⊕ Δ ⇒s Ξ} {τ : Θ ⊕ Γ ⇒s Δ}
    → ((extend-sˡ {Γ = Δ} {Δ = Ξ} {Ξ = Λ} σ) ∘s (extend-sˡ τ)) ≈s extend-sˡ {Γ = Γ} {Δ = Ξ} {Ξ = Λ} (σ ∘s τ)
  ∘s-extendˡ (var-inr x) = eq-refl
  ∘s-extendˡ {Γ = Γ} {Δ = Δ} {Ξ = Ξ} {σ = σ} (var-inl x)  = ∘s-extendˡ-aux {Γ = Δ} {Δ = Γ} {t = σ x}
    where
      ∘s-extendˡ-aux : ∀ {Θ Γ Δ Ξ A} {τ : Θ ⊕ Δ ⇒s Γ} {t : Term Θ Γ A}
        → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ ([ var-inl ]r t) [ extend-sˡ τ ]s ≈ [ var-inl ]r (t [ τ ]s) ⦂ A
      ∘s-extendˡ-aux {t = tm-var x} = eq-refl
      ∘s-extendˡ-aux {t = tm-meta M ts} = eq-congr-mv λ i → ∘s-extendˡ-aux {t = ts i}
      ∘s-extendˡ-aux {τ = τ} {t = tm-oper f es} = eq-congr λ i → extend-var-inl (es i) τ

  ∘ˢ-≈aux :  ∀ {Θ Γ Δ Ξ Λ A} {t : Term Θ (Γ ,, Λ) A} {σ : Θ ⊕ Δ ⇒ˢ Γ} {τ : Θ ⊕ Ξ ⇒ˢ Δ}
    → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ (t [ ⇑ˢ σ ]ˢ) [ ⇑ˢ τ ]ˢ ≈ (t [ (⇑ˢ σ) ∘ˢ (⇑ˢ τ) ]ˢ) ⦂ A

  -- extension of substitutions preserves equality of substitutions
  ≈s-extend-sˡ : ∀ {Θ Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒s Δ}
    → σ ≈s τ
    → extend-sˡ {Θ} {Γ} {Δ} {Ξ} σ ≈s extend-sˡ {Θ} {Γ} {Δ} {Ξ} τ

  -- composition of substitutions preserves equality of substitutions
  ∘s-≈s : ∀ {Θ Γ Δ Ξ} {δ : Θ ⊕ Δ ⇒s Γ} {σ τ : Θ ⊕ Ξ ⇒s Δ}
    → σ ≈s τ
    → (δ ∘s σ) ≈s (δ ∘s τ)
  ∘s-≈s {δ = δ} eq x = subst-congr {t = δ x} eq

  -- equality of substitutions is commutative
  ≈s-comm : ∀ {Θ Γ Δ} {σ τ : Θ ⊕ Δ ⇒s Γ}
    → σ ≈s τ
    → τ ≈s σ
  ≈s-comm eq x = eq-symm (eq x)

  -- composition of a substitution and a renaming is a substitution
  s∘r≈s : ∀ {Θ Γ Δ Ξ} {ρ : Θ ⊕ Δ ⇒r Ξ} {σ : Θ ⊕ Δ ⇒s Γ}
    → (σ s∘r ρ) ≈s (σ ∘s (r-to-subst ρ))
  s∘r≈s x = r-to-subst-≈

  -- composition of a renaming and a substitition is also a substitution
  r∘s≈s : ∀ {Θ Γ Δ Ξ} {ρ : Θ ⊕ Γ ⇒r Δ} {σ : Θ ⊕ Ξ ⇒s Δ}
    → ((r-to-subst ρ) ∘s σ) ≈s (ρ r∘s σ)
  r∘s≈s x = eq-refl


  -- substitution commutes with renamings when acting on terms
  s-comm-r : ∀ {Θ Γ Δ Ξ A} {ρ : Θ ⊕ Γ ⇒r Δ} {σ : Θ ⊕ Ξ ⇒s Δ} (t : Term Θ Γ A)
             → ⊢ Θ ⊕ Ξ ∥ ([ ρ ]r t) [ σ ]s ≈ t [ ρ r∘s σ ]s ⦂ A
  s-comm-r (tm-var x) = eq-refl
  s-comm-r (tm-meta M ts) = eq-congr-mv λ i → s-comm-r (ts i)
  s-comm-r (tm-oper f es) = eq-congr λ i → s-comm-r-aux (es i)
    module Extras where
      s-comm-r-aux : ∀ {Θ Γ Δ Ξ Λ A} {ρ : Θ ⊕ Γ ⇒r Δ} {σ : Θ ⊕ Ξ ⇒s Δ} (t : Term Θ (Γ ,, Λ) A)
        → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ ([ extend-r {Θ = Θ} ρ ]r t) [ extend-sˡ σ ]s ≈ t [ extend-sˡ (ρ r∘s σ) ]s ⦂ A
      s-comm-r-aux {Θ} {Γ} {Δ} {Ξ} {Λ} {A} {ρ} {σ} t =
        let open SetoidR (eq-setoid (Ξ ,, Λ) Θ A) in
          begin
            ([ extend-r ρ ]r t) [ extend-sˡ σ ]s ≈⟨ ≈tm-subst {s = [ extend-r ρ ]r t} r-to-subst-≈ ⟩
            ((t [ r-to-subst (extend-r ρ) ]s) [ extend-sˡ σ ]s) ≈⟨ ∘s-≈ {t = t} ⟩
            (t [ (r-to-subst (extend-r ρ)) ∘s extend-sˡ σ ]s) ≈⟨ (subst-congr {t = t}) (λ _ → eq-refl) ⟩
            (t [ (extend-r ρ) r∘s extend-sˡ σ ]s) ≈⟨ subst-congr {t = t} ext-r-ext-s≈ext-s ⟩
            (t [ extend-sˡ (ρ r∘s σ) ]s)
          ∎
        where
        ext-r-ext-s≈ext-s : ∀ {Θ Γ Δ Ξ Λ} {ρ : Θ ⊕ Γ ⇒r Δ} {σ : Θ ⊕ Ξ ⇒s Δ}
          → ((extend-r {Θ = Θ} ρ {Λ}) r∘s (extend-sˡ σ)) ≈s (extend-sˡ (ρ r∘s σ))
        ext-r-ext-s≈ext-s (var-inl x) = eq-refl
        ext-r-ext-s≈ext-s (var-inr y) = eq-refl
          
  -- renaming commutes with substitution when acting on terms
  r-comm-s : ∀ {Θ Γ Δ Ξ A} (σ : Θ ⊕ Δ ⇒s Γ) (ρ : Θ ⊕ Δ ⇒r Ξ) (t : Term Θ Γ A)
    → ⊢ Θ ⊕ Ξ ∥ [ ρ ]r (t [ σ ]s) ≈ t [ σ s∘r ρ ]s ⦂ A
  r-comm-s σ ρ (tm-var x) = eq-refl
  r-comm-s σ ρ (tm-meta M ts) = eq-congr-mv (λ i → r-comm-s σ ρ (ts i))
  r-comm-s σ ρ (tm-oper f es) = eq-congr (λ i → r-comm-s-aux (es i))
    where
      r-comm-s-aux : ∀ {Θ Γ Δ Ξ Λ A} {σ : Θ ⊕ Δ ⇒s Γ} {ρ : Θ ⊕ Δ ⇒r Ξ} (t : Term Θ (Γ ,, Λ) A)
        → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ ([ extend-r {Θ} ρ ]r (t [ extend-sˡ σ ]s)) ≈ t [ extend-sˡ (σ s∘r ρ) ]s ⦂ A
      r-comm-s-aux {Θ} {Γ} {Δ} {Ξ} {Λ} {A} {σ} {ρ} t =
        let open SetoidR (eq-setoid (Ξ ,, Λ) Θ A) in
          begin
            (([ extend-r {Θ} ρ ]r (t [ extend-sˡ σ ]s)))
              ≈⟨ r-to-subst-≈ ⟩
            ((t [ extend-sˡ σ ]s) [ r-to-subst (extend-r {Θ} ρ) ]s)
              ≈⟨ ∘s-≈ {t = t} ⟩
            (t [ ( extend-sˡ σ) ∘s (r-to-subst (extend-r {Θ} ρ)) ]s )
              ≈⟨ subst-congr {t = t} (∘s-≈s {δ = ( extend-sˡ σ)}  r-to-subst-comm-ext) ⟩
            (t [ ( extend-sˡ σ) ∘s (extend-sˡ (r-to-subst ρ)) ]s )
              ≈⟨ subst-congr {t = t} ∘s-extendˡ ⟩  -- ∘s-extendˡ
            (t [ extend-sˡ (σ ∘s (r-to-subst ρ)) ]s)
              ≈⟨ subst-congr {t = t} (≈s-extend-sˡ (≈s-comm (s∘r≈s {ρ = ρ} {σ = σ}))) ⟩
            (t [ extend-sˡ (σ s∘r ρ) ]s)
          ∎
        where
        r-to-subst-comm-ext : ∀ {Θ Γ Δ Ξ} {ρ : Θ ⊕ Γ ⇒r Δ}
          → (r-to-subst {Θ} (extend-r {Θ} ρ {Ξ})) ≈s (extend-sˡ (r-to-subst ρ))
        r-to-subst-comm-ext (var-inl x) = eq-refl
        r-to-subst-comm-ext (var-inr y) = eq-refl



  --==================================================================================================
  --∥                                    ====================                                        ∥
  --∥                                    ∥   ** Proofs **   ∥                                        ∥
  --∥                                    ====================                                        ∥
  --==================================================================================================

  ------------------------------------------------------------------------------------------------------
  -- I.
  r-to-subst ρ x = tm-var (ρ x)


  r-to-subst-⇑ˢ (var-inl x) = eq-refl
  r-to-subst-⇑ˢ (var-inr x) = eq-refl


  r-to-subst-≈ {t = tm-var x} = eq-refl
  r-to-subst-≈ {t = tm-meta M ts} = eq-meta λ i → r-to-subst-≈
  r-to-subst-≈ {t = tm-oper f es} = eq-oper λ i → r-to-subst-≈aux

  r-to-subst-≈aux {Θ = Θ} {Γ = Γ} {Δ = Δ} {t = t} {ρ = ρ} = eq-trans r-to-subst-≈ (subst-congr {t = t} (r-to-subst-⇑ˢ {ρ = ρ}))


  --------------------------------------------------------------------------------------------------------
  -- II.
  -- A.
  subst-congr {t = Signature.tm-var x} p = p x
  subst-congr {t = Signature.tm-meta M ts} p = eq-meta λ i → subst-congr {t = ts i} p
  subst-congr {t = Signature.tm-oper f es} p = eq-oper λ i → subst-congr-aux {t = es i} p

  id-action {a = tm-var x} = eq-refl
  id-action {a = tm-meta M ts} = eq-meta λ i → id-action
  id-action {a = tm-oper f es} = eq-oper λ i → eq-trans id-action-aux (eq-symm (subst-congr {t = es i} λ x → idˢ-extendˡ))
    where
      id-action-aux : ∀ {Θ Γ Ξ A} {t : Term Θ (Γ ,, Ξ) A} → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ t ≈  (t [ idˢ ]ˢ) ⦂ A
      id-action-aux = id-action

  ≈tm-subst eq-refl = eq-refl
  ≈tm-subst (eq-symm p) = eq-symm (≈tm-subst p)
  ≈tm-subst (eq-trans p₁ p₂) = eq-trans (≈tm-subst p₁) (≈tm-subst p₂)
  ≈tm-subst (eq-oper x) = eq-oper λ i → ≈tm-subst (x i) -- needs an auxiliary function
  ≈tm-subst (eq-meta ps) = eq-meta λ i → ≈tm-subst (ps i)
  ≈tm-subst (eq-axiom ε I) = {!!} -- Should we find a way to "compose" substitution and instantiation so as to get an instatiation ? We also have to take care of the renaming with empty context

  ∘ˢ-≈ {t = tm-var x} = eq-refl
  ∘ˢ-≈ {t = tm-meta M ts} = eq-meta λ i → ∘ˢ-≈ {t = ts i}
  ∘ˢ-≈ {t = tm-oper f es} {σ = σ} {τ = τ} = eq-oper λ i → eq-trans (∘ˢ-≈aux {t = es i} {σ = σ} {τ = τ}) (subst-congr {t = es i} {σ =  ⇑ˢ σ ∘ˢ ⇑ˢ τ} {τ = ⇑ˢ (σ ∘ˢ τ)} ∘ˢ-extendˡ)


  -- B.
  idˢ-extendˡ {a = var-inl a} = eq-refl
  idˢ-extendˡ {a = var-inr a} = eq-refl

  ∘ˢ-extendˡ (var-inr x) = eq-refl
  ∘ˢ-extendˡ {Γ = Γ} {Δ = Δ} {Ξ = Ξ} {σ = σ} (var-inl x)  = ∘ˢ-extendˡ-aux {Γ = Δ} {Δ = Γ} {t = σ x}

  ∘ˢ-extendˡ-aux {t = tm-var x} = eq-refl
  ∘ˢ-extendˡ-aux {t = tm-meta M ts} = eq-meta λ i → ∘ˢ-extendˡ-aux {t = ts i}
  ∘ˢ-extendˡ-aux {τ = τ} {t = tm-oper f es} = eq-oper λ i → extend-var-inl (es i) τ

  ∘ˢ-≈aux {Γ = Γ} {Λ = Λ} {t = tm-var x}  {σ = σ} = ∘ˢ-≈ {Γ = (Γ ,, Λ)} {t = tm-var x} {σ = ⇑ˢ σ}
  ∘ˢ-≈aux {t = tm-meta M ts} = eq-meta λ i → ∘ˢ-≈aux {t = ts i}
  ∘ˢ-≈aux {t = tm-oper f es} {σ = σ} {τ = τ} = eq-oper λ i → eq-trans (∘ˢ-≈aux {t = es i}) (subst-congr {t = es i} {σ = ⇑ˢ (⇑ˢ σ) ∘ˢ ⇑ˢ (⇑ˢ τ)} {τ = ⇑ˢ (⇑ˢ σ ∘ˢ ⇑ˢ τ)} ∘ˢ-extendˡ)


  ≈ˢ-⇑ˢ p (var-inl x) = ≈ˢ-⇑ʳ p
  ≈ˢ-⇑ˢ p (var-inr x) = eq-refl

  subst-congr-aux {Γ = Γ} {Ξ = Ξ} {t = t} p = subst-congr {Γ = Γ ,, Ξ} {t = t} λ x → ≈ˢ-⇑ˢ p x



  --==================================================================================================
  --∥                                    ==========================                                  ∥
  --∥                                    ∥   ** Corollaries **    ∥                                 ∥
  --∥                                    ==========================                                  ∥
  --==================================================================================================



  subst-congr₂ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {σ τ : Θ ⊕ Δ ⇒ˢ Γ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → σ ≈ˢ τ → ⊢ Θ ⊕ Δ ∥ s [ σ ]ˢ ≈  t [ τ ]ˢ ⦂ A
  subst-congr₂ {s = s} pt ps = eq-trans (subst-congr {t = s} ps) (≈tm-subst pt)
