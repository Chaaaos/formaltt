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

module SecondOrder.MetaTheorem {ℓ ℓs ℓo ℓa : Level}
                               {𝔸 : Arity}
                               {Σ : SecondOrderSignature.Signature {ℓs} {ℓo} {ℓa} 𝔸}
                               {T : SecondOrderTheory.Theory {ℓs} {ℓo} {ℓa} {𝔸} {Σ} ℓ} where

  open SecondOrderSignature {ℓs} {ℓo} {ℓa} 𝔸
  open Signature Σ
  open SecondOrder.Substitution {ℓs} {ℓo} {ℓa} {𝔸} {Σ}
  open SecondOrderTheory {ℓs} {ℓo} {ℓa} {𝔸} {Σ}
  open Theory {ℓ} T


  -- terms and judgemental equality form a setoid
  eq-setoid : ∀ (Γ : Context) (Θ : MetaContext) (A : sort) → Setoid (lsuc (ℓo ⊔ ℓs ⊔ ℓa )) (lsuc (ℓ ⊔ ℓo ⊔ ℓs ⊔ ℓa))
  eq-setoid Γ Θ A =
    record
      { Carrier = Term Θ Γ A
      ;  _≈_ = λ s t → (⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A)
      ; isEquivalence =
                      record
                        { refl = eq-refl
                        ; sym = eq-symm
                        ; trans = eq-trans
                        }
        }


-- The following theorems are mostly interdependant, so the way we declare them is a bit different

  --===================================================================================================
  --∥                                    ====================                                         ∥
  --∥                                    ∥  ** Theorems **  ∥                                         ∥
  --∥                                    ====================                                         ∥
  --===================================================================================================

  --===================================================================================================

  --==================
  -- I. Renamings    ∥
  --==================

  ---------------------
  -- A. Main theorems |
  ---------------------
  
  -- renamings preserve equality of terms
  r-congr : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : _⇒r_ {Θ = Θ} Γ Δ}
    → _≈r_ {Θ = Θ} σ τ
    → ⊢ Θ ⊕ Δ ∥ t [ σ ]r ≈  t [ τ ]r ⦂ A
    
  -- renaming preserves equality of terms
  ≈tm-rename : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : _⇒r_ {Θ} Γ Δ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A
    → ⊢ Θ ⊕ Δ ∥ tm-rename ρ s ≈ tm-rename ρ t ⦂ A
    
  -- action of renaming commutes with composition
  ∘r-≈ :  ∀ {Θ Γ Δ Ξ A} {t : Term Θ Γ A} {σ : _⇒r_ {Θ} Γ Δ} {τ : _⇒r_ {Θ} Δ Ξ}
    → ⊢ Θ ⊕ Ξ ∥ (t [ σ ]r) [ τ ]r ≈ (t [ _∘r_ {Θ = Θ} τ σ ]r) ⦂ A
    
  -- action of the identity renaming is the identity
  id-action-r : ∀ {Θ Γ A} {a : Term Θ Γ A} → (⊢ Θ ⊕ Γ ∥ a ≈ (a [ (id-r {Θ = Θ}) ]r) ⦂ A)
  
  ------------------------------
  -- B. Lemmas and corollaries |
  ------------------------------

  -- extension preserves equality of renamings
  ≈r-extend-r : ∀ {Θ : MetaContext} {Γ Δ Ξ} {σ τ : _⇒r_ {Θ = Θ} Γ Δ}
    → _≈r_ {Γ} {Δ} {Θ} σ τ
    → _≈r_ {Γ ,, Ξ} {Δ ,, Ξ} {Θ} (extend-r {Θ} {Γ} {Δ} σ) (extend-r {Θ} {Γ} {Δ} τ)
  ≈r-extend-r {σ = σ} {τ = τ} p (var-inl x) = ≈tm-rename (p x)
  ≈r-extend-r p (var-inr x) = eq-refl

  -- interactions between extensions
  extend-var-inl : ∀ {Γ Δ Ξ Λ Θ A} (t : Term Θ (Λ ,, Ξ) A) (τ : Γ ⇒s Λ)
    → ⊢ Θ ⊕ ((Γ ,, Δ) ,, Ξ) ∥
        ((tm-rename (extend-r {Θ = Θ} var-inl) t) [ extend-sˡ (extend-sˡ τ) ]s)
      ≈ (tm-rename (extend-r {Θ = Θ} var-inl) (t [ extend-sˡ τ ]s)) ⦂ A
      
  -- auxiliary function for id-action-r, with extended context
  id-action-r-aux : ∀ {Θ Γ Ξ A} {a : Term Θ (Γ ,, Ξ) A}
    → (⊢ Θ ⊕ (Γ ,, Ξ) ∥ a ≈ (a [ (id-r {Θ = Θ}) ]r) ⦂ A)
    
  -- auxiliary function : the extension of the identity renaming is the identity
  id-r-extend : ∀ {Θ Γ Ξ A} {a : A ∈ (Γ ,, Ξ)}
    → ⊢ Θ ⊕ (Γ ,, Ξ) ∥
         tm-var (extend-r {Θ} {Γ} {Γ} (id-r {Θ = Θ} {Γ = Γ}) {Ξ} a)
       ≈ tm-var (id-r {Θ = Θ} {Γ = Γ ,, Ξ} a) ⦂ A

  ---------------------------------------------------------------------------------------------
  --=================================
  -- II. Renamings to substitutions ∥
  --=================================
  
  -- enables to use a renaming as a substitution
  r-to-subst : ∀ {Θ Γ Δ} (ρ : _⇒r_ {Θ} Γ Δ) → _⇒s_ {Θ} Δ Γ

  syntax r-to-subst ρ = ρ ˢ
  
  r-to-subst-extend-sˡ : ∀ {Θ Γ Δ Ξ} {ρ : _⇒r_ {Θ} Γ Δ}
    →  _≈s_ {Θ = Θ} (r-to-subst (extend-r {Θ = Θ} ρ {Ξ = Ξ})) (extend-sˡ (r-to-subst ρ))

  -- For any renaming ρ and term t, it doesn't matter if we act on t with
  -- the renaming ρ or act on t with the substitution induced by ρ
  -- Proposition 3.19 (1)
  r-to-subst-≈ :  ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {ρ : _⇒r_ {Θ = Θ} Γ Δ}
    → ⊢ Θ ⊕ Δ ∥ (tm-rename ρ t) ≈ t [ r-to-subst ρ ]s ⦂ A

  -- applying an extended renaming (ρ ⊕ Ξ) on a term t is the same as extending the
  -- substitution induced by the renaming ρ
  r-to-subst-≈aux : ∀ {Θ Γ Δ Ξ A} {t : Term Θ (Γ ,, Ξ) A} {ρ : _⇒r_ {Θ} Γ Δ}
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ (tm-rename (extend-r {Θ = Θ} ρ) t) ≈ t [ extend-sˡ (r-to-subst ρ) ]s ⦂ A

  ---------------------------------------------------------------------------------------------
  --=====================
  -- III. Substitutions ∥
  --=====================

  ---------------------
  -- A. Main theorems |
  ---------------------
  
  -- actions of equal substitutions are pointwise equal
  subst-congr : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Δ ⇒s Γ}
    → σ ≈s τ → ⊢ Θ ⊕ Δ ∥ t [ σ ]s ≈  t [ τ ]s ⦂ A
    
  -- action of the identity substitution is the identity
  -- Proposition 3.19 (2)
  id-action : ∀ {Θ Γ A} {a : Term Θ Γ A}
    → (⊢ Θ ⊕ Γ ∥ a ≈ (a [ id-s ]s) ⦂ A)
    
  -- substitution preserves equality of terms
  ≈tm-subst : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {σ : Δ ⇒s Γ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Δ ∥ s [ σ ]s ≈  t [ σ ]s ⦂ A
    
  -- action of substitutions "commutes" with composition, i.e. is functorial
  -- Proposition 3.19 (4)
  ∘s-≈ :  ∀ {Θ Γ Δ Ξ A} {t : Term Θ Γ A} {σ : _⇒s_ {Θ} Δ Γ} {τ : _⇒s_ {Θ} Ξ Δ}
    → ⊢ Θ ⊕ Ξ ∥ (t [ σ ]s) [ τ ]s ≈ (t [ σ ∘s τ ]s) ⦂ A

  --------------
  -- B. Lemmas |
  --------------

  -- weakening preserves equality of substitutions
  ≈s-weakenˡ : ∀ {Θ Γ Δ Ξ A} {σ τ : Δ ⇒s Γ} {x : A ∈ Γ}
    → σ ≈s τ
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ weakenˡ (σ x) ≈ weakenˡ (τ x) ⦂ A
  
  -- extension of the identity substitution is the identity substitution
  id-s-extendˡ : ∀ {Θ Γ Ξ A} {a : A ∈ (Γ ,, Ξ)}
    → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ extend-sˡ {Θ} {Γ} {Γ} {Ξ} (id-s {Γ = Γ}) {A} a ≈  id-s {Γ = Γ ,, Ξ} a ⦂ A
    
  subst-congr-aux : ∀ {Θ Γ Δ Ξ A} {t : Term Θ (Γ ,, Ξ) A} {σ τ : Δ ⇒s Γ}
    → σ ≈s τ → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ t [ extend-sˡ σ ]s ≈  t [ extend-sˡ τ ]s ⦂ A
    
  -- extension of substitutions preserve composition
  ∘s-extendˡ : ∀ {Θ Γ Δ Ξ Λ} {σ : _⇒s_ {Θ} Δ Ξ} {τ : _⇒s_ {Θ} Γ Δ}
    → ((extend-sˡ {Γ = Δ} {Δ = Ξ} {Ξ = Λ} σ) ∘s (extend-sˡ τ)) ≈s extend-sˡ {Γ = Γ} {Δ = Ξ} {Ξ = Λ} (σ ∘s τ)
    
  ∘s-extendˡ-aux : ∀ {Θ Γ Δ Ξ A} {τ : _⇒s_ {Θ} Δ Γ} {t : Term Θ Γ A}
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ tm-rename var-inl t [ extend-sˡ τ ]s ≈ tm-rename var-inl (t [ τ ]s) ⦂ A
    
  ∘s-≈aux :  ∀ {Θ Γ Δ Ξ Λ A} {t : Term Θ (Γ ,, Λ) A} {σ : _⇒s_ {Θ} Δ Γ} {τ : _⇒s_ {Θ} Ξ Δ}
    → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ (t [ extend-sˡ σ ]s) [ extend-sˡ τ ]s ≈ (t [ (extend-sˡ σ) ∘s (extend-sˡ τ) ]s) ⦂ A
    
  -- extension of substitutions preserves equality of substitutions
  ≈s-extend-sˡ : ∀ {Θ Γ Δ Ξ} {σ τ : Γ ⇒s Δ}
    → σ ≈s τ
    → extend-sˡ {Θ} {Γ} {Δ} {Ξ} σ ≈s extend-sˡ {Θ} {Γ} {Δ} {Ξ} τ

  --
  temp : ∀ {Θ Γ Δ Ξ Ψ A} (ρ : _⇒r_ {Θ} Γ Δ)  (σ : _⇒s_ {Θ} Ξ Δ) (t : Term Θ (Γ ,, Ψ) A)
    → ⊢ Θ ⊕ (Ξ ,, Ψ) ∥ t [ (λ x → (extend-sˡ σ) ((extend-r {Θ} {Γ} {Δ} ρ {Ψ}) x)) ]s ≈ t [ extend-sˡ (λ x → σ (ρ x)) ]s ⦂ A
  temp ρ σ (tm-var (var-inl x)) = eq-refl
  temp ρ σ (tm-var (var-inr x)) = eq-refl
  temp ρ σ (tm-meta M ts) = eq-congr-mv λ i → temp ρ σ (ts i)
  temp {Θ} {Γ} {Δ} {Ξ} {Ψ} ρ σ (tm-oper f es) =
    eq-congr (λ i → temp (extend-r {Θ} {Γ} {Δ} ρ {Ψ}) (extend-sˡ σ) {!es i!})
    

  -- substitution commutes with renamings
  s-comm-r : ∀ {Θ Γ Δ Ξ A} (ρ : _⇒r_ {Θ} Γ Δ)  (σ : _⇒s_ {Θ} Ξ Δ)  (t : Term Θ Γ A)
    → ⊢ Θ ⊕ Ξ ∥ (t [ ρ ]r) [ σ ]s ≈ t [ (λ x → σ (ρ x)) ]s ⦂ A
  s-comm-r ρ σ (tm-var x) = eq-refl
  s-comm-r ρ σ (tm-meta M ts) = eq-congr-mv (λ i → s-comm-r ρ σ (ts i))
  s-comm-r ρ σ (tm-oper f es) = eq-congr λ i
    → s-comm-r (extend-r ρ) (extend-sˡ σ) {!es i!}

  r-comm-s : ∀ {Θ Γ Δ Ξ A} (σ : _⇒s_ {Θ} Δ Γ) (ρ : _⇒r_ {Θ} Δ Ξ) (t : Term Θ Γ A)
    → ⊢ Θ ⊕ Ξ ∥ (t [ σ ]s) [ ρ ]r ≈ t [ (λ x → (σ x) [ ρ ]r) ]s ⦂ A
  r-comm-s σ ρ (tm-var x) = eq-refl
  r-comm-s σ ρ (tm-meta M ts) = eq-congr-mv (λ i → r-comm-s σ ρ (ts i))
  r-comm-s σ ρ (tm-oper f es) = eq-congr (λ i → r-comm-s (extend-sˡ σ) (extend-r ρ) {!es i!})

  -----------------------------------------------------------------------------------------------------

  --==============================
  -- IV. Metavariable extensions ∥
  --==============================

  ------------------
  -- Main Theorems |
  ------------------
  
  -- actions of equal metavariable instantiations are pointwise equal
  mv-inst-congr : ∀ {Θ ψ Γ Δ A} {t : Term Θ Δ A} {ι μ : ψ ⇒M Θ ⊕ Γ}
    → ι ≈M μ → ⊢ ψ ⊕ (Γ ,, Δ) ∥ t [ ι ]M ≈ t [ μ ]M ⦂ A
    
  -- action of a metavariable instantiation preserves equality of terms
  ≈tm-mv-inst : ∀ {Θ ψ Γ Δ A} {s t : Term Θ Δ A} {ι : ψ ⇒M Θ ⊕ Γ}
    → ⊢ Θ ⊕ Δ ∥ s ≈ t ⦂ A
    → ⊢ ψ ⊕ (Γ ,, Δ) ∥ s [ ι ]M ≈ t [ ι ]M ⦂ A
    
  -- action of metavariable instantiations "commutes" with composition
  ∘M-≈aux : ∀ {Θ ψ Ω Γ Δ Ξ A} {t : Term Θ Γ A} {ι : Ω ⇒M ψ ⊕ Ξ } {μ : ψ ⇒M Θ ⊕ Δ} → ⊢ Ω ⊕ ((Ξ ,, Δ) ,, Γ) ∥ term-reassoc ((t [ μ ]M) [ ι ]M) ≈ (t [ ι ∘M μ ]M) ⦂ A

  -- action of the identity metavariable is the identity
  id-action-mv : ∀ {Θ Γ A} {a : Term Θ Γ A}
    → (⊢ Θ ⊕ (ctx-empty ,, Γ) ∥ weakenʳ a ≈ (a [ id-M ]M) ⦂ A)

<<<<<<< HEAD

  -- action of substitution on an instantiation
  -- temp : ∀ {Θ ψ Γ Δ A} {s t : Term Θ Δ A} {ι : ψ ⇒M Θ ⊕ Δ} {σ : Δ ⇒s Γ}
  --   → 

  --==================================================================================================
  --∥                                    ====================                                        ∥
  --∥                                    ∥   ** Proofs **   ∥                                        ∥
  --∥                                    ====================                                        ∥
  --==================================================================================================
=======
  -- B. Lemmas
  tm-rename-empty-≈ : ∀ {Θ Γ A} {s t : Term Θ (Γ ,, ctx-empty) A} → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Γ ∥ tm-rename (rename-ctx-empty-r {Θ = Θ}) s ≈ tm-rename (rename-ctx-empty-r {Θ = Θ}) t ⦂ A
  term-reassoc-≈ : ∀ {Θ Δ Γ Ξ A} {s t : Term Θ (Γ ,, (Δ ,, Ξ)) A} → ⊢ Θ ⊕ ((Γ ,, Δ) ,, Ξ) ∥ term-reassoc s ≈ term-reassoc t ⦂ A → ⊢ Θ ⊕ (Γ ,, (Δ ,, Ξ)) ∥ s ≈ t ⦂ A
  -- ** Proofs **
>>>>>>> second-order

  -------------------------------------------------------------------------------------------
  -- I.
  -- A.
  

  r-congr {t = tm-var x} p = p x
  r-congr {t = tm-meta M ts} p = eq-congr-mv λ i → r-congr p
  r-congr {t = tm-oper f es} p = eq-congr λ i → r-congr (≈r-extend-r p)

  ≈tm-rename eq-refl = eq-refl
  ≈tm-rename (eq-symm p) = eq-symm (≈tm-rename p)
  ≈tm-rename (eq-trans p₁ p₂) = eq-trans (≈tm-rename p₁) (≈tm-rename p₂)
  ≈tm-rename (eq-congr p) = eq-congr λ i → ≈tm-rename (p i)
  ≈tm-rename (eq-congr-mv p) = eq-congr-mv λ i → ≈tm-rename (p i)
  ≈tm-rename {ρ = ρ} (eq-axiom ε ι) = {!!} -- I have no idea how one could solve this for the moment

  ∘r-≈ {t = tm-var x} = eq-refl
  ∘r-≈ {t = tm-meta M ts} = eq-congr-mv λ i → ∘r-≈
  ∘r-≈ {t = tm-oper f es} = eq-congr λ i → {!!} -- needs an auxialiary function

  id-action-r {a = tm-var x} = eq-refl
  id-action-r {a = tm-meta M ts} = eq-congr-mv λ i → id-action-r
  id-action-r {a = tm-oper f es} = eq-congr λ i → eq-trans id-action-r-aux (eq-symm (r-congr λ x → id-r-extend))

  -- B.
  ≈s-weakenˡ {x = x} p = ≈tm-rename (p x)

  extend-var-inl (tm-var x) τ = {!!}
  extend-var-inl (tm-meta M ts) τ = {!!}
  extend-var-inl (tm-oper f es) τ = {!!}

  id-action-r-aux = id-action-r

  id-r-extend {a = var-inl a} = eq-refl
  id-r-extend {a = var-inr a} = eq-refl

  ------------------------------------------------------------------------------------------------------
  -- II.
  r-to-subst ρ x = tm-var (ρ x)


  r-to-subst-extend-sˡ (var-inl x) = eq-refl
  r-to-subst-extend-sˡ (var-inr x) = eq-refl


  r-to-subst-≈ {t = tm-var x} = eq-refl
  r-to-subst-≈ {t = tm-meta M ts} = eq-congr-mv λ i → r-to-subst-≈
  r-to-subst-≈ {t = tm-oper f es} = eq-congr λ i → r-to-subst-≈aux

  r-to-subst-≈aux {Θ = Θ} {Γ = Γ} {Δ = Δ} {t = t} {ρ = ρ} = eq-trans r-to-subst-≈ (subst-congr {t = t} (r-to-subst-extend-sˡ {ρ = ρ}))


  --------------------------------------------------------------------------------------------------------
  -- III.
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

  ≈tm-subst eq-refl = eq-refl
  ≈tm-subst (eq-symm p) = eq-symm (≈tm-subst p)
  ≈tm-subst (eq-trans p₁ p₂) = eq-trans (≈tm-subst p₁) (≈tm-subst p₂)
  ≈tm-subst (eq-congr x) = eq-congr λ i → ≈tm-subst (x i) -- needs an auxiliary function
  ≈tm-subst (eq-congr-mv ps) = eq-congr-mv λ i → ≈tm-subst (ps i)
  ≈tm-subst (eq-axiom ε ι) = {!!} -- Should we find a way to "compose" substitution and instantiation so as to get an instatiation ?

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


  ≈s-extend-sˡ p (var-inl x) = ≈s-weakenˡ p
  ≈s-extend-sˡ p (var-inr x) = eq-refl

  subst-congr-aux {Γ = Γ} {Ξ = Ξ} {t = t} p = subst-congr {Γ = Γ ,, Ξ} {t = t} λ x → ≈s-extend-sˡ p x

  -- IV.
  -- A.

  mv-inst-congr {t = tm-var x} p = eq-refl
  mv-inst-congr {t = tm-meta M ts} p = subst-congr λ x → {!!}
  mv-inst-congr {t = tm-oper f es} p = eq-congr λ i → {!!}

  ≈tm-mv-inst eq-refl = eq-refl
  ≈tm-mv-inst (eq-symm p) = eq-symm (≈tm-mv-inst p)
  ≈tm-mv-inst (eq-trans p₁ p₂) = eq-trans (≈tm-mv-inst p₁) (≈tm-mv-inst p₂)
  ≈tm-mv-inst (eq-congr x) = eq-congr λ i → {!!}
  ≈tm-mv-inst (eq-congr-mv x) = subst-congr λ x₁ → {!!}
  ≈tm-mv-inst (eq-axiom ε ι) =  mv-inst-congr {!!} -- define the composition of mv instantiations


  id-action-mv {a = tm-var x} = eq-refl
  id-action-mv {a = tm-meta M ts} = eq-congr-mv λ i → id-action-mv
  id-action-mv {a = tm-oper f es} = eq-congr λ i → id-action-mv-aux -- needs an auxiliary function
    where
      id-action-mv-aux : ∀ {Θ Γ Δ A} {t : Term Θ (Γ ,, Δ) A} → ⊢ Θ ⊕ ((ctx-empty ,, Γ) ,, Δ) ∥ tm-rename (extend-r {Θ = Θ} var-inr) t ≈ tm-rename (rename-assoc-l {Θ = Θ}) (t [ id-M ]M) ⦂ A
      id-action-mv-aux {t = tm-var (var-inl x)} = eq-refl
      id-action-mv-aux {t = tm-var (var-inr x)} = eq-refl
      id-action-mv-aux {t = tm-meta M ts} = eq-congr-mv λ i → id-action-mv-aux
      id-action-mv-aux {t = tm-oper f es} = eq-congr λ i → {!id-action-mv-aux!}


  ∘M-≈aux {t = tm-var x} = eq-refl
  ∘M-≈aux {t = tm-meta M ts} = {!!}
  ∘M-≈aux {t = tm-oper f es} = eq-congr λ i → {!!} -- needs an auxiliary function


  -- B.
  term-reassoc-≈ p = {!p!}

  tm-rename-empty-≈ = {!!}



 -- the lhs and rhs of an equation are equal

  eq-axiom-id-aux : ∀ {Θ Γ A} {s t : Term Θ Γ A} → ⊢ Θ ⊕ (ctx-empty ,, Γ) ∥ weakenʳ s ≈ weakenʳ t ⦂ A → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A
  eq-axiom-id-aux p = {!!}

  eq-axiom-id : ∀ (ε : ax) → ⊢ ((ax-mv-ctx ε) ⊕ ctx-empty ∥ ax-lhs ε ≈ ax-rhs ε ⦂  (ax-sort ε))
  eq-axiom-id ε = eq-axiom-id-aux (eq-trans id-action-mv (eq-symm (eq-trans id-action-mv (eq-symm {!!})))) -- doesn't work, problem with contexts (I am not even sure that it akes sense to try to prove this - maybe some definitions are wrong ?)
