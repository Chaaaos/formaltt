-- {-# OPTIONS --allow-unsolved-metas #-}

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
  r-to-subst : ∀ {Θ Γ Δ} (ρ : Θ ⊕ Γ ⇒r Δ) → Θ ⊕ Δ ⇒s Γ

  syntax r-to-subst ρ = ρ ˢ

  r-to-subst-extend-sˡ : ∀ {Θ Γ Δ Ξ} {ρ : Θ ⊕ Γ ⇒r Δ}
    →  _≈s_ {Θ = Θ} (r-to-subst (extend-r {Θ = Θ} ρ {Ξ = Ξ})) (extend-sˡ (r-to-subst ρ))

  -- For any renaming ρ and term t, it doesn't matter if we act on t with
  -- the renaming ρ or act on t with the substitution induced by ρ
  -- Proposition 3.19 (1)
  r-to-subst-≈ :  ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {ρ : Θ ⊕ Γ ⇒r Δ}
    → ⊢ Θ ⊕ Δ ∥ ([ ρ ]r t) ≈ t [ r-to-subst ρ ]s ⦂ A

  -- applying an extended renaming (ρ ⊕ Ξ) on a term t is the same as extending the
  -- substitution induced by the renaming ρ
  r-to-subst-≈aux : ∀ {Θ Γ Δ Ξ A} {t : Term Θ (Γ ,, Ξ) A} {ρ : Θ ⊕ Γ ⇒r Δ}
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ ([(extend-r {Θ = Θ} ρ)]r t) ≈ t [ extend-sˡ (r-to-subst ρ) ]s ⦂ A

  ---------------------------------------------------------------------------------------------
  --=====================
  -- II. Substitutions ∥
  --=====================

  ---------------------
  -- A. Main theorems |
  ---------------------

  -- actions of equal substitutions are pointwise equal
  subst-congr : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Θ ⊕ Δ ⇒s Γ}
    → σ ≈s τ → ⊢ Θ ⊕ Δ ∥ t [ σ ]s ≈  t [ τ ]s ⦂ A

  -- action of the identity substitution is the identity
  -- Proposition 3.19 (2)
  id-action : ∀ {Θ Γ A} {a : Term Θ Γ A}
    → (⊢ Θ ⊕ Γ ∥ a ≈ (a [ id-s ]s) ⦂ A)

  -- substitution preserves equality of terms
  ≈tm-subst : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {σ : Θ ⊕ Δ ⇒s Γ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Δ ∥ s [ σ ]s ≈  t [ σ ]s ⦂ A

  -- action of substitutions "commutes" with composition, i.e. is functorial
  -- Proposition 3.19 (4)
  ∘s-≈ :  ∀ {Θ Γ Δ Ξ A} {t : Term Θ Γ A} {σ : Θ ⊕ Δ ⇒s Γ} {τ : Θ ⊕ Ξ ⇒s Δ}
    → ⊢ Θ ⊕ Ξ ∥ (t [ σ ]s) [ τ ]s ≈ (t [ σ ∘s τ ]s) ⦂ A

  --------------
  -- B. Lemmas |
  --------------

  -- extension of the identity substitution is the identity substitution
  id-s-extendˡ : ∀ {Θ Γ Ξ A} {a : A ∈ (Γ ,, Ξ)}
    → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ extend-sˡ {Θ} {Γ} {Γ} {Ξ} (id-s {Γ = Γ}) {A} a ≈  id-s {Γ = Γ ,, Ξ} a ⦂ A

  subst-congr-aux : ∀ {Θ Γ Δ Ξ A} {t : Term Θ (Γ ,, Ξ) A} {σ τ : Θ ⊕ Δ ⇒s Γ}
    → σ ≈s τ → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ t [ extend-sˡ σ ]s ≈  t [ extend-sˡ τ ]s ⦂ A

  -- extension of substitutions preserve composition
  ∘s-extendˡ : ∀ {Θ Γ Δ Ξ Λ} {σ : Θ ⊕ Δ ⇒s Ξ} {τ : Θ ⊕ Γ ⇒s Δ}
    → ((extend-sˡ {Γ = Δ} {Δ = Ξ} {Ξ = Λ} σ) ∘s (extend-sˡ τ)) ≈s extend-sˡ {Γ = Γ} {Δ = Ξ} {Ξ = Λ} (σ ∘s τ)

  ∘s-extendˡ-aux : ∀ {Θ Γ Δ Ξ A} {τ : Θ ⊕ Δ ⇒s Γ} {t : Term Θ Γ A}
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ ([ var-inl ]r t) [ extend-sˡ τ ]s ≈ [ var-inl ]r (t [ τ ]s) ⦂ A

  ∘s-≈aux :  ∀ {Θ Γ Δ Ξ Λ A} {t : Term Θ (Γ ,, Λ) A} {σ : Θ ⊕ Δ ⇒s Γ} {τ : Θ ⊕ Ξ ⇒s Δ}
    → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ (t [ extend-sˡ σ ]s) [ extend-sˡ τ ]s ≈ (t [ (extend-sˡ σ) ∘s (extend-sˡ τ) ]s) ⦂ A

  -- extension of substitutions preserves equality of substitutions
  ≈s-extend-sˡ : ∀ {Θ Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒s Δ}
    → σ ≈s τ
    → extend-sˡ {Θ} {Γ} {Δ} {Ξ} σ ≈s extend-sˡ {Θ} {Γ} {Δ} {Ξ} τ


  -- temp2 : ∀ {Θ Γ Δ Ξ Ψ} {ρ : _⇒r_ {Θ} Γ Δ} {σ : _⇒s_ {Θ} Ξ Δ}
  --   → ((extend-sˡ {Θ} {Ξ} {Δ} {Ψ} σ) s∘r (extend-r {Θ} {Γ} {Δ} ρ {Ψ})) ≈s extend-sˡ (σ s∘r ρ)
  -- temp2 (var-inl x) = eq-refl
  -- temp2 (var-inr y) = eq-refl

  -- temp : ∀ {Θ Γ Δ Ξ Ψ A} (ρ : _⇒r_ {Θ} Γ Δ)  (σ : _⇒s_ {Θ} Ξ Δ) (t : Term Θ (Γ ,, Ψ) A)
  --   → ⊢ Θ ⊕ (Ξ ,, Ψ) ∥ t [ (λ x → (extend-sˡ σ) ((extend-r {Θ} {Γ} {Δ} ρ {Ψ}) x)) ]s ≈ t [ extend-sˡ (λ x → σ (ρ x)) ]s ⦂ A
  -- temp {Θ} {Γ} {Δ} {Ξ} {Ψ} {A} ρ σ t = subst-congr temp2


  temp3 : ∀ {Θ Γ Δ Ξ} (ρ : Θ ⊕ Δ ⇒r Ξ) (σ : Θ ⊕ Δ ⇒s Γ)
    → (σ s∘r ρ) ≈s (σ ∘s (r-to-subst ρ))
  temp3 ρ σ x = r-to-subst-≈

  -- interactions between extensions
  extend-var-inl : ∀ {Γ Δ Ξ Λ Θ A} (t : Term Θ (Λ ,, Ξ) A) (τ : Θ ⊕ Γ ⇒s Λ)
    → ⊢ Θ ⊕ ((Γ ,, Δ) ,, Ξ) ∥
        (([ (extend-r {Θ = Θ} var-inl) ]r t) [ extend-sˡ (extend-sˡ τ) ]s)
      ≈ ([ (extend-r {Θ = Θ} var-inl) ]r (t [ extend-sˡ τ ]s)) ⦂ A

  -- substitution commutes with renamings
  s-comm-r : ∀ {Θ Γ Δ Ξ A} {ρ : Θ ⊕ Γ ⇒r Δ} {σ : Θ ⊕ Ξ ⇒s Δ} (t : Term Θ Γ A)
             → ⊢ Θ ⊕ Ξ ∥ ([ ρ ]r t) [ σ ]s ≈ t [ ρ r∘s σ ]s ⦂ A
  s-comm-r {Θ} {Γ} {Δ} {Ξ} {A} {ρ = ρ} {σ = σ} (tm-var x) = eq-refl
  s-comm-r {Θ} {Γ} {Δ} {Ξ} {ρ = ρ} {σ = σ} (tm-meta M ts) = eq-congr-mv λ i → s-comm-r (ts i)
  s-comm-r {Θ} {Γ} {Δ} {Ξ} {ρ = ρ} {σ = σ} (tm-oper f es) = eq-congr λ i → s-comm-r-aux (es i)
    where
      s-comm-r-aux : ∀ {Θ Γ Δ Ξ Λ A} {ρ : Θ ⊕ Γ ⇒r Δ} {σ : Θ ⊕ Ξ ⇒s Δ} (t : Term Θ (Γ ,, Λ) A)
                     → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ ([ extend-r {Θ = Θ} ρ ]r t) [ extend-sˡ σ ]s ≈ t [ extend-sˡ (ρ r∘s σ) ]s ⦂ A
      s-comm-r-aux (tm-var (var-inl x)) = eq-refl
      s-comm-r-aux (tm-var (var-inr x)) = eq-refl
      s-comm-r-aux (tm-meta M ts) = eq-congr-mv λ i → s-comm-r-aux (ts i)
      s-comm-r-aux {Θ = Θ} (tm-oper f es) = eq-congr λ i → eq-trans (extend-var-inl {!!} {!σ!}) {!!}



  -- s-comm-r (tm-var x) = eq-refl
  -- s-comm-r (tm-meta M ts) = eq-congr-mv (λ i → s-comm-r (ts i))
  -- s-comm-r {Θ} {Γ} {Δ} {Ξ} {A} {ρ = ρ} {σ = σ} (tm-oper f es) = eq-congr λ i → {!tm-oper f es!}

  -- s-comm-r {Θ} {Γ} {Δ} {Ξ} {A} {ρ = ρ} {σ = σ} (tm-oper f es) =
  --   eq-congr λ i → temp {Θ} {Γ} {Δ} {Ξ} {(arg-bind f i)} {(arg-sort f i)} ρ σ {!es i!}

  -- renaming commutes with substitution
  -- r-comm-s : ∀ {Θ Γ Δ Ξ A} (σ : _⇒s_ {Θ} Ξ Δ) (ρ : _⇒r_ {Θ} Γ Δ) (t : Term Θ Γ A)
  --   → ⊢ Θ ⊕ Ξ ∥ (t [ σ ]s) [ ρ ]r ≈ t [ σ s∘r ρ ]s ⦂ A
  -- r-comm-s σ ρ (tm-var x) = eq-refl
  -- r-comm-s σ ρ (tm-meta M ts) = eq-congr-mv (λ i → r-comm-s σ ρ (ts i))
  -- r-comm-s σ ρ (tm-oper f es) = eq-congr (λ i → r-comm-s (extend-sˡ σ) (extend-r ρ) {!es i!})






  --==================================================================================================
  --∥                                    ====================                                        ∥
  --∥                                    ∥   ** Proofs **   ∥                                        ∥
  --∥                                    ====================                                        ∥
  --==================================================================================================

  ------------------------------------------------------------------------------------------------------
  -- I.
  r-to-subst ρ x = tm-var (ρ x)


  r-to-subst-extend-sˡ (var-inl x) = eq-refl
  r-to-subst-extend-sˡ (var-inr x) = eq-refl


  r-to-subst-≈ {t = tm-var x} = eq-refl
  r-to-subst-≈ {t = tm-meta M ts} = eq-congr-mv λ i → r-to-subst-≈
  r-to-subst-≈ {t = tm-oper f es} = eq-congr λ i → r-to-subst-≈aux

  r-to-subst-≈aux {Θ = Θ} {Γ = Γ} {Δ = Δ} {t = t} {ρ = ρ} = eq-trans r-to-subst-≈ (subst-congr {t = t} (r-to-subst-extend-sˡ {ρ = ρ}))


  --------------------------------------------------------------------------------------------------------
  -- II.
  -- A.
  subst-congr {t = Signature.tm-var x} p = p x
  subst-congr {t = Signature.tm-meta M ts} p = eq-congr-mv λ i → subst-congr {t = ts i} p
  subst-congr {t = Signature.tm-oper f es} p = eq-congr λ i → subst-congr-aux {t = es i} p

  id-action {a = tm-var x} = eq-refl
  id-action {a = tm-meta M ts} = eq-congr-mv λ i → id-action
  id-action {a = tm-oper f es} = eq-congr λ i → eq-trans id-action-aux (eq-symm (subst-congr {t = es i} λ x → id-s-extendˡ))
    where
      id-action-aux : ∀ {Θ Γ Ξ A} {t : Term Θ (Γ ,, Ξ) A} → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ t ≈  (t [ id-s ]s) ⦂ A
      id-action-aux = id-action

  s∘M-≈ : ∀ {Θ ψ Γ Δ A} {t : Term Θ ctx-empty A} {σ : ψ ⊕ Δ ⇒s Γ} {ι : ψ ⇒M Θ ⊕ Γ}
          → ⊢ ψ ⊕ Δ ∥ (([ rename-ctx-empty-r {Θ = ψ} ]r (t [ ι ]M)) [ σ ]s) ≈ ([ rename-ctx-empty-r {Θ = ψ} ]r (t [ σ s∘M ι ]M)) ⦂ A
  s∘M-≈ {t = tm-meta M ts} = {!!}
  s∘M-≈ {t = tm-oper f es} = {!!}

  ≈tm-subst eq-refl = eq-refl
  ≈tm-subst (eq-symm p) = eq-symm (≈tm-subst p)
  ≈tm-subst (eq-trans p₁ p₂) = eq-trans (≈tm-subst p₁) (≈tm-subst p₂)
  ≈tm-subst (eq-congr x) = eq-congr λ i → ≈tm-subst (x i) -- needs an auxiliary function
  ≈tm-subst (eq-congr-mv ps) = eq-congr-mv λ i → ≈tm-subst (ps i)
  ≈tm-subst {σ = σ} (eq-axiom ε ι) = eq-trans
                                       (s∘M-≈ {t = ax-lhs ε})
                                       (eq-trans
                                         (eq-axiom ε (σ s∘M ι))
                                         (eq-symm (s∘M-≈ {t = ax-rhs ε})))


  ∘s-≈ {t = tm-var x} = eq-refl
  ∘s-≈ {t = tm-meta M ts} = eq-congr-mv λ i → ∘s-≈ {t = ts i}
  ∘s-≈ {t = tm-oper f es} {σ = σ} {τ = τ} = eq-congr λ i → eq-trans (∘s-≈aux {t = es i} {σ = σ} {τ = τ}) (subst-congr {t = es i} {σ =  extend-sˡ σ ∘s extend-sˡ τ} {τ = extend-sˡ (σ ∘s τ)} ∘s-extendˡ)


  -- B.
  id-s-extendˡ {a = var-inl a} = eq-refl
  id-s-extendˡ {a = var-inr a} = eq-refl

  ∘s-extendˡ (var-inr x) = eq-refl
  ∘s-extendˡ {Γ = Γ} {Δ = Δ} {Ξ = Ξ} {σ = σ} (var-inl x)  = ∘s-extendˡ-aux {Γ = Δ} {Δ = Γ} {t = σ x}

  ∘s-extendˡ-aux {t = tm-var x} = eq-refl
  ∘s-extendˡ-aux {t = tm-meta M ts} = eq-congr-mv λ i → ∘s-extendˡ-aux {t = ts i}
  ∘s-extendˡ-aux {τ = τ} {t = tm-oper f es} = eq-congr λ i → extend-var-inl (es i) τ

  ∘s-≈aux {Γ = Γ} {Λ = Λ} {t = tm-var x}  {σ = σ} = ∘s-≈ {Γ = (Γ ,, Λ)} {t = tm-var x} {σ = extend-sˡ σ}
  ∘s-≈aux {t = tm-meta M ts} = eq-congr-mv λ i → ∘s-≈aux {t = ts i}
  ∘s-≈aux {t = tm-oper f es} {σ = σ} {τ = τ} = eq-congr λ i → eq-trans (∘s-≈aux {t = es i}) (subst-congr {t = es i} {σ = extend-sˡ (extend-sˡ σ) ∘s extend-sˡ (extend-sˡ τ)} {τ = extend-sˡ (extend-sˡ σ ∘s extend-sˡ τ)} ∘s-extendˡ)



  extend-var-inl (tm-var (var-inl x)) τ = ?
  extend-var-inl (tm-var (var-inr x)) τ = {!!}
  extend-var-inl (tm-meta M ts) τ = {!!}
  extend-var-inl (tm-oper f es) τ = {!!}


  ≈s-extend-sˡ p (var-inl x) = ≈s-weakenˡ p
  ≈s-extend-sˡ p (var-inr x) = eq-refl

  subst-congr-aux {Γ = Γ} {Ξ = Ξ} {t = t} p = subst-congr {Γ = Γ ,, Ξ} {t = t} λ x → ≈s-extend-sˡ p x



  --==================================================================================================
  --∥                                    ==========================                                  ∥
  --∥                                    ∥   ** Corollaries **    ∥                                 ∥
  --∥                                    ==========================                                  ∥
  --==================================================================================================



  subst-congr₂ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {σ τ : Θ ⊕ Δ ⇒s Γ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → σ ≈s τ → ⊢ Θ ⊕ Δ ∥ s [ σ ]s ≈  t [ τ ]s ⦂ A
  subst-congr₂ {s = s} pt ps = eq-trans (subst-congr {t = s} ps) (≈tm-subst pt)
