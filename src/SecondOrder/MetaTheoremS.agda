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
    →  _≈s_ {Θ = Θ} (r-to-subst (extendʳ {Θ = Θ} ρ {Ξ = Ξ})) (⇑ˢ (r-to-subst ρ))

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
    → σ ≈s τ → ⊢ Θ ⊕ Δ ∥ t [ σ ]ˢ ≈  t [ τ ]ˢ ⦂ A

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
    → σ ≈s τ → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ t [ ⇑ˢ σ ]ˢ ≈  t [ ⇑ˢ τ ]ˢ ⦂ A

  -- extension of substitutions preserve composition
  ∘ˢ-extendˡ : ∀ {Θ Γ Δ Ξ Λ} {σ : Θ ⊕ Δ ⇒ˢ Ξ} {τ : Θ ⊕ Γ ⇒ˢ Δ}
    → ((⇑ˢ {Γ = Δ} {Δ = Ξ} {Ξ = Λ} σ) ∘ˢ (⇑ˢ τ)) ≈s ⇑ˢ {Γ = Γ} {Δ = Ξ} {Ξ = Λ} (σ ∘ˢ τ)

  ∘ˢ-extendˡ-aux : ∀ {Θ Γ Δ Ξ A} {τ : Θ ⊕ Δ ⇒ˢ Γ} {t : Term Θ Γ A}
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ ([ var-inl ]ʳ t) [ ⇑ˢ τ ]ˢ ≈ [ var-inl ]ʳ (t [ τ ]ˢ) ⦂ A

  ∘ˢ-≈aux :  ∀ {Θ Γ Δ Ξ Λ A} {t : Term Θ (Γ ,, Λ) A} {σ : Θ ⊕ Δ ⇒ˢ Γ} {τ : Θ ⊕ Ξ ⇒ˢ Δ}
    → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ (t [ ⇑ˢ σ ]ˢ) [ ⇑ˢ τ ]ˢ ≈ (t [ (⇑ˢ σ) ∘ˢ (⇑ˢ τ) ]ˢ) ⦂ A

  -- extension of substitutions preserves equality of substitutions
  ≈s-⇑ˢ : ∀ {Θ Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒ˢ Δ}
    → σ ≈s τ
    → ⇑ˢ {Θ} {Γ} {Δ} {Ξ} σ ≈s ⇑ˢ {Θ} {Γ} {Δ} {Ξ} τ


  -- temp2 : ∀ {Θ Γ Δ Ξ Ψ} {ρ : _⇒ʳ_ {Θ} Γ Δ} {σ : _⇒ˢ_ {Θ} Ξ Δ}
  --   → ((⇑ˢ {Θ} {Ξ} {Δ} {Ψ} σ) s∘ʳ (extendʳ {Θ} {Γ} {Δ} ρ {Ψ})) ≈s ⇑ˢ (σ s∘ʳ ρ)
  -- temp2 (var-inl x) = eq-refl
  -- temp2 (var-inr y) = eq-refl

  -- temp : ∀ {Θ Γ Δ Ξ Ψ A} (ρ : _⇒ʳ_ {Θ} Γ Δ)  (σ : _⇒ˢ_ {Θ} Ξ Δ) (t : Term Θ (Γ ,, Ψ) A)
  --   → ⊢ Θ ⊕ (Ξ ,, Ψ) ∥ t [ (λ x → (⇑ˢ σ) ((extendʳ {Θ} {Γ} {Δ} ρ {Ψ}) x)) ]ˢ ≈ t [ ⇑ˢ (λ x → σ (ρ x)) ]ˢ ⦂ A
  -- temp {Θ} {Γ} {Δ} {Ξ} {Ψ} {A} ρ σ t = subst-congr temp2


  temp3 : ∀ {Θ Γ Δ Ξ} (ρ : Θ ⊕ Δ ⇒ʳ Ξ) (σ : Θ ⊕ Δ ⇒ˢ Γ)
    → (σ s∘ʳ ρ) ≈s (σ ∘ˢ (r-to-subst ρ))
  temp3 ρ σ x = r-to-subst-≈

  -- substitution commutes with renamings
  s-comm-r : ∀ {Θ Γ Δ Ξ A} {ρ : Θ ⊕ Γ ⇒ʳ Δ} {σ : Θ ⊕ Ξ ⇒ˢ Δ} (t : Term Θ Γ A)
    → ⊢ Θ ⊕ Ξ ∥ ([ ρ ]ʳ t) [ σ ]ˢ ≈ t [ ρ ʳ⃗ˢ ∘ˢ σ ]ˢ ⦂ A
  s-comm-r {Θ} {Γ} {Δ} {Ξ} {A} {ρ = ρ} {σ = σ} t = {!!}

  -- s-comm-r (tm-var x) = eq-refl
  -- s-comm-r (tm-meta M ts) = eq-congr-mv (λ i → s-comm-r (ts i))
  -- s-comm-r {Θ} {Γ} {Δ} {Ξ} {A} {ρ = ρ} {σ = σ} (tm-oper f es) = eq-congr λ i → {!tm-oper f es!}

  -- s-comm-r {Θ} {Γ} {Δ} {Ξ} {A} {ρ = ρ} {σ = σ} (tm-oper f es) =
  --   eq-congr λ i → temp {Θ} {Γ} {Δ} {Ξ} {(arg-bind f i)} {(arg-sort f i)} ρ σ {!es i!}

  -- renaming commutes with substitution
  -- r-comm-s : ∀ {Θ Γ Δ Ξ A} (σ : _⇒ˢ_ {Θ} Ξ Δ) (ρ : _⇒ʳ_ {Θ} Γ Δ) (t : Term Θ Γ A)
  --   → ⊢ Θ ⊕ Ξ ∥ (t [ σ ]ˢ) [ ρ ]ʳ ≈ t [ σ s∘ʳ ρ ]ˢ ⦂ A
  -- r-comm-s σ ρ (tm-var x) = eq-refl
  -- r-comm-s σ ρ (tm-meta M ts) = eq-congr-mv (λ i → r-comm-s σ ρ (ts i))
  -- r-comm-s σ ρ (tm-oper f es) = eq-congr (λ i → r-comm-s (⇑ˢ σ) (extendʳ ρ) {!es i!})






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
  r-to-subst-≈ {t = tm-meta M ts} = eq-congr-mv λ i → r-to-subst-≈
  r-to-subst-≈ {t = tm-oper f es} = eq-congr λ i → r-to-subst-≈aux

  r-to-subst-≈aux {Θ = Θ} {Γ = Γ} {Δ = Δ} {t = t} {ρ = ρ} = eq-trans r-to-subst-≈ (subst-congr {t = t} (r-to-subst-⇑ˢ {ρ = ρ}))


  --------------------------------------------------------------------------------------------------------
  -- II.
  -- A.
  subst-congr {t = Signature.tm-var x} p = p x
  subst-congr {t = Signature.tm-meta M ts} p = eq-congr-mv λ i → subst-congr {t = ts i} p
  subst-congr {t = Signature.tm-oper f es} p = eq-congr λ i → subst-congr-aux {t = es i} p

  id-action {a = tm-var x} = eq-refl
  id-action {a = tm-meta M ts} = eq-congr-mv λ i → id-action
  id-action {a = tm-oper f es} = eq-congr λ i → eq-trans id-action-aux (eq-symm (subst-congr {t = es i} λ x → idˢ-extendˡ))
    where
      id-action-aux : ∀ {Θ Γ Ξ A} {t : Term Θ (Γ ,, Ξ) A} → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ t ≈  (t [ idˢ ]ˢ) ⦂ A
      id-action-aux = id-action

  ≈tm-subst eq-refl = eq-refl
  ≈tm-subst (eq-symm p) = eq-symm (≈tm-subst p)
  ≈tm-subst (eq-trans p₁ p₂) = eq-trans (≈tm-subst p₁) (≈tm-subst p₂)
  ≈tm-subst (eq-congr x) = eq-congr λ i → ≈tm-subst (x i) -- needs an auxiliary function
  ≈tm-subst (eq-congr-mv ps) = eq-congr-mv λ i → ≈tm-subst (ps i)
  ≈tm-subst (eq-axiom ε ι) = {!!} -- Should we find a way to "compose" substitution and instantiation so as to get an instatiation ? We also have to take care of the renaming with empty context

  ∘ˢ-≈ {t = tm-var x} = eq-refl
  ∘ˢ-≈ {t = tm-meta M ts} = eq-congr-mv λ i → ∘ˢ-≈ {t = ts i}
  ∘ˢ-≈ {t = tm-oper f es} {σ = σ} {τ = τ} = eq-congr λ i → eq-trans (∘ˢ-≈aux {t = es i} {σ = σ} {τ = τ}) (subst-congr {t = es i} {σ =  ⇑ˢ σ ∘ˢ ⇑ˢ τ} {τ = ⇑ˢ (σ ∘ˢ τ)} ∘ˢ-extendˡ)


  -- B.
  idˢ-extendˡ {a = var-inl a} = eq-refl
  idˢ-extendˡ {a = var-inr a} = eq-refl

  ∘ˢ-extendˡ (var-inr x) = eq-refl
  ∘ˢ-extendˡ {Γ = Γ} {Δ = Δ} {Ξ = Ξ} {σ = σ} (var-inl x)  = ∘ˢ-extendˡ-aux {Γ = Δ} {Δ = Γ} {t = σ x}

  ∘ˢ-extendˡ-aux {t = tm-var x} = eq-refl
  ∘ˢ-extendˡ-aux {t = tm-meta M ts} = eq-congr-mv λ i → ∘ˢ-extendˡ-aux {t = ts i}
  ∘ˢ-extendˡ-aux {τ = τ} {t = tm-oper f es} = eq-congr λ i → extend-var-inl (es i) τ

  ∘ˢ-≈aux {Γ = Γ} {Λ = Λ} {t = tm-var x}  {σ = σ} = ∘ˢ-≈ {Γ = (Γ ,, Λ)} {t = tm-var x} {σ = ⇑ˢ σ}
  ∘ˢ-≈aux {t = tm-meta M ts} = eq-congr-mv λ i → ∘ˢ-≈aux {t = ts i}
  ∘ˢ-≈aux {t = tm-oper f es} {σ = σ} {τ = τ} = eq-congr λ i → eq-trans (∘ˢ-≈aux {t = es i}) (subst-congr {t = es i} {σ = ⇑ˢ (⇑ˢ σ) ∘ˢ ⇑ˢ (⇑ˢ τ)} {τ = ⇑ˢ (⇑ˢ σ ∘ˢ ⇑ˢ τ)} ∘ˢ-extendˡ)


  ≈s-⇑ˢ p (var-inl x) = ≈s-⇑ʳ p
  ≈s-⇑ˢ p (var-inr x) = eq-refl

  subst-congr-aux {Γ = Γ} {Ξ = Ξ} {t = t} p = subst-congr {Γ = Γ ,, Ξ} {t = t} λ x → ≈s-⇑ˢ p x



  --==================================================================================================
  --∥                                    ==========================                                  ∥
  --∥                                    ∥   ** Corollaries **    ∥                                 ∥
  --∥                                    ==========================                                  ∥
  --==================================================================================================



  subst-congr₂ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {σ τ : Θ ⊕ Δ ⇒ˢ Γ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → σ ≈s τ → ⊢ Θ ⊕ Δ ∥ s [ σ ]ˢ ≈  t [ τ ]ˢ ⦂ A
  subst-congr₂ {s = s} pt ps = eq-trans (subst-congr {t = s} ps) (≈tm-subst pt)
