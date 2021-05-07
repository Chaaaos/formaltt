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
  r-congr : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Θ ⊕ Γ ⇒ʳ Δ}
    → _≈r_ {Θ = Θ} σ τ
    → ⊢ Θ ⊕ Δ ∥ [ σ ]ʳ t ≈ [ τ ]ʳ t ⦂ A

  -- renaming preserves equality of terms
  ≈tm-rename : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Θ ⊕ Γ ⇒ʳ Δ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A
    → ⊢ Θ ⊕ Δ ∥ [ ρ ]ʳ s ≈ [ ρ ]ʳ t ⦂ A

  -- action of renaming commutes with composition
  ∘ʳ-≈ :  ∀ {Θ Γ Δ Ξ A} {t : Term Θ Γ A} {σ : Θ ⊕ Γ ⇒ʳ Δ} {τ : Θ ⊕ Δ ⇒ʳ Ξ}
    → ⊢ Θ ⊕ Ξ ∥ [ τ ]ʳ ([ σ ]ʳ t) ≈ ([ _∘ʳ_ {Θ = Θ} τ σ ]ʳ t) ⦂ A

  -- action of the identity renaming is the identity
  id-action-r : ∀ {Θ Γ A} {a : Term Θ Γ A} → (⊢ Θ ⊕ Γ ∥ a ≈ ([ (idʳ {Θ = Θ}) ]ʳ a) ⦂ A)

  ------------------------------
  -- B. Lemmas and corollaries |
  ------------------------------

  -- extension preserves equality of renamings
  ≈r-extendʳ : ∀ {Θ : MetaContext} {Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒ʳ Δ}
    → σ ≈r τ
    → _≈r_ {Γ ,, Ξ} {Δ ,, Ξ} (extendʳ {Θ} {Γ} {Δ} σ) (extendʳ {Θ} {Γ} {Δ} τ)
  ≈r-extendʳ {Θ} {Γ} {Δ} {Ξ} {σ = σ} {τ = τ} p (var-inl x) = ≈tm-rename {ρ = var-inl} (p x)
  ≈r-extendʳ p (var-inr x) = eq-refl

  -- interactions between extensions
  extend-var-inl : ∀ {Γ Δ Ξ Λ Θ A} (t : Term Θ (Λ ,, Ξ) A) (τ : Θ ⊕ Γ ⇒ˢ Λ)
    → ⊢ Θ ⊕ ((Γ ,, Δ) ,, Ξ) ∥
        (([ (extendʳ {Θ = Θ} var-inl) ]ʳ t) [ ⇑ˢ (⇑ˢ τ) ]ˢ)
      ≈ ([ (extendʳ {Θ = Θ} var-inl) ]ʳ (t [ ⇑ˢ τ ]ˢ)) ⦂ A

  -- auxiliary function for id-action-r, with extended context
  id-action-r-aux : ∀ {Θ Γ Ξ A} {a : Term Θ (Γ ,, Ξ) A}
    → (⊢ Θ ⊕ (Γ ,, Ξ) ∥ a ≈ ([ (idʳ {Θ = Θ}) ]ʳ a) ⦂ A)

  -- auxiliary function : the extension of the identity renaming is the identity
  idʳ-extend : ∀ {Θ Γ Ξ A} {a : A ∈ (Γ ,, Ξ)}
    → ⊢ Θ ⊕ (Γ ,, Ξ) ∥
         tm-var (extendʳ {Θ} {Γ} {Γ} (idʳ {Θ = Θ} {Γ = Γ}) {Ξ} a)
       ≈ tm-var (idʳ {Θ = Θ} {Γ = Γ ,, Ξ} a) ⦂ A

  ---------------------------------------------------------------------------------------------
  --=================================
  -- II. Renamings to substitutions ∥
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
  -- III. Substitutions ∥
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

  -- weakening preserves equality of substitutions
  ≈s-⇑ʳ : ∀ {Θ Γ Δ Ξ A} {σ τ : Θ ⊕ Δ ⇒ˢ Γ} {x : A ∈ Γ}
    → σ ≈s τ
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ ⇑ʳ (σ x) ≈ ⇑ʳ (τ x) ⦂ A

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
    → ⊢ Θ ⊕ Ξ ∥ ([ ρ ]ʳ t) [ σ ]ˢ ≈ t [ ρ r∘ˢ σ ]ˢ ⦂ A
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
  ≈tm-mv-inst : ∀ {Θ ψ Γ Δ A} {s t : Term Θ Δ A} {μ : ψ ⇒M Θ ⊕ Γ}
                → ⊢ Θ ⊕ Δ ∥ s ≈ t ⦂ A
                → ⊢ ψ ⊕ (Γ ,, Δ) ∥ s [ μ ]M ≈ t [ μ ]M ⦂ A

  -- action of metavariable instantiations "commutes" with composition
  ∘M-≈ : ∀ {Θ ψ Ω Γ Δ Ξ A} {t : Term Θ Γ A} {ι : Ω ⇒M ψ ⊕ Ξ } {μ : ψ ⇒M Θ ⊕ Δ}
         → ⊢ Ω ⊕ ((Ξ ,, Δ) ,, Γ) ∥ term-reassoc ((t [ μ ]M) [ ι ]M) ≈ (t [ ι ∘M μ ]M) ⦂ A

  -- action of the identity metavariable is the identity
  id-action-mv : ∀ {Θ Γ A} {a : Term Θ Γ A}
                 → (⊢ Θ ⊕ (ctx-empty ,, Γ) ∥ weakenʳ a ≈ (a [ id-M ]M) ⦂ A)


  -- B. Lemmas


  term-reassoc-≈ : ∀ {Θ Δ Γ Ξ A} {s t : Term Θ (Γ ,, (Δ ,, Ξ)) A}
                   → ⊢ Θ ⊕ ((Γ ,, Δ) ,, Ξ) ∥ term-reassoc s ≈ term-reassoc t ⦂ A
                   → ⊢ Θ ⊕ (Γ ,, (Δ ,, Ξ)) ∥ s ≈ t ⦂ A
  []M-mv-congr : ∀ {Θ ψ Γ Δ A} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)
                 (ι μ : ψ ⇒M Θ ⊕ Δ) (x : A ∈ (Δ ,, mv-arity Θ M))
                 → ι ≈M μ → ⊢ ψ ⊕ (Δ ,, Γ) ∥ []M-mv M ts ι x ≈ []M-mv M ts μ x ⦂ A
  -- mv-inst-congr-mv : ∀ {Θ ψ Γ Δ A} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)  (ι μ : ψ ⇒M Θ ⊕ Δ) (x : A ∈ (Δ ,, mv-arity Θ M))  → ι ≈M μ → ⊢ ψ ⊕ (Δ ,, Γ) ∥ mv-subst-mv {A = A} M ts ι x ≈ mv-subst-mv {A = A} M ts μ x ⦂ A

  --==================================================================================================
  --∥                                    ====================                                        ∥
  --∥                                    ∥   ** Proofs **   ∥                                        ∥
  --∥                                    ====================                                        ∥
  --==================================================================================================

  -------------------------------------------------------------------------------------------
  -- I.
  -- A.


  r-congr {t = tm-var x} p = p x
  r-congr {t = tm-meta M ts} p = eq-congr-mv λ i → r-congr p
  r-congr {t = tm-oper f es} p = eq-congr λ i → r-congr (≈r-extendʳ p)

  ≈tm-rename eq-refl = eq-refl
  ≈tm-rename (eq-symm p) = eq-symm (≈tm-rename p)
  ≈tm-rename (eq-trans p₁ p₂) = eq-trans (≈tm-rename p₁) (≈tm-rename p₂)
  ≈tm-rename (eq-congr p) = eq-congr λ i → ≈tm-rename (p i)
  ≈tm-rename (eq-congr-mv p) = eq-congr-mv λ i → ≈tm-rename (p i)
  ≈tm-rename {ρ = ρ} (eq-axiom ε ι) = {!!} -- I have no idea how one could solve this for the moment

  ∘ʳ-≈ {t = tm-var x} = eq-refl
  ∘ʳ-≈ {t = tm-meta M ts} = eq-congr-mv λ i → ∘ʳ-≈
  ∘ʳ-≈ {t = tm-oper f es} = eq-congr λ i → {!!} -- needs an auxialiary function

  id-action-r {a = tm-var x} = eq-refl
  id-action-r {a = tm-meta M ts} = eq-congr-mv λ i → id-action-r
  id-action-r {a = tm-oper f es} = eq-congr λ i → eq-trans id-action-r-aux (eq-symm (r-congr λ x → idʳ-extend))

  -- B.
  ≈s-⇑ʳ {x = x} p = ≈tm-rename (p x)

  extend-var-inl (tm-var x) τ = {!!}
  extend-var-inl (tm-meta M ts) τ = {!!}
  extend-var-inl (tm-oper f es) τ = {!!}

  id-action-r-aux = id-action-r

  idʳ-extend {a = var-inl a} = eq-refl
  idʳ-extend {a = var-inr a} = eq-refl

  ------------------------------------------------------------------------------------------------------
  -- II.
  r-to-subst ρ x = tm-var (ρ x)


  r-to-subst-⇑ˢ (var-inl x) = eq-refl
  r-to-subst-⇑ˢ (var-inr x) = eq-refl


  r-to-subst-≈ {t = tm-var x} = eq-refl
  r-to-subst-≈ {t = tm-meta M ts} = eq-congr-mv λ i → r-to-subst-≈
  r-to-subst-≈ {t = tm-oper f es} = eq-congr λ i → r-to-subst-≈aux

  r-to-subst-≈aux {Θ = Θ} {Γ = Γ} {Δ = Δ} {t = t} {ρ = ρ} = eq-trans r-to-subst-≈ (subst-congr {t = t} (r-to-subst-⇑ˢ {ρ = ρ}))


  --------------------------------------------------------------------------------------------------------
  -- III.
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

  -- IV.
  -- A.

  []M-mv-congr M ts ι μ (var-inl x) p = eq-refl
  []M-mv-congr M ts ι μ (var-inr x) p = mv-inst-congr {t = ts x} p

  []M-mv-≈ : ∀ {Θ ψ Γ Δ} (M : mv Θ) (xs ys : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)
             (ι : ψ ⇒M Θ ⊕ Δ) → (∀ {B} (i : mv-arg Θ M B) → ⊢ Θ ⊕ Γ ∥ xs i ≈ ys i ⦂ B )
             → []M-mv M xs ι ≈s []M-mv M ys ι
  []M-mv-≈ M xs ys ι ps (var-inl x) = eq-refl
  []M-mv-≈ M xs ys ι ps (var-inr x) = ≈tm-mv-inst (ps x)

  subst-congr₂ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {σ τ : Θ ⊕ Δ ⇒ˢ Γ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → σ ≈s τ → ⊢ Θ ⊕ Δ ∥ s [ σ ]ˢ ≈  t [ τ ]ˢ ⦂ A
  subst-congr₂ {s = s} pt ps = eq-trans (subst-congr {t = s} ps) (≈tm-subst pt)


  mv-inst-congr {t = tm-var x} p = eq-refl
  mv-inst-congr {t = tm-meta M ts} {ι = ι} {μ = μ} p = subst-congr₂ (p M) λ x → []M-mv-congr M ts ι μ x p
  mv-inst-congr {t = tm-oper f es} p = eq-congr λ i → ≈tm-rename (mv-inst-congr {t = es i} p)

  ≈empty-ctx-rename-inv : ∀ {Θ Γ A} {t s : Term Θ Γ A}
                          → ⊢ Θ ⊕ Γ ∥ t ≈ s ⦂ A
                          → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ [ rename-ctx-empty-inv {Θ = Θ} ]ʳ t ≈ [ rename-ctx-empty-inv {Θ = Θ} ]ʳ s ⦂ A
  ≈empty-ctx-rename-inv = ≈tm-rename

  empty-ctx-rename-inv-l : ∀ {Θ Γ A} {t : Term Θ (Γ ,, ctx-empty) A}
                           → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ [ rename-ctx-empty-inv {Θ = Θ} ]ʳ ([ rename-ctx-empty-r {Θ = Θ} ]ʳ t) ≈ t ⦂ A
  empty-ctx-rename-inv-l {t = tm-var (var-inl x)} = eq-refl
  empty-ctx-rename-inv-l {t = tm-meta M ts} = eq-congr-mv λ i → empty-ctx-rename-inv-l
  empty-ctx-rename-inv-l {t = tm-oper f es} = eq-congr λ i → {!!}

  empty-ctx-rename-inv-r : ∀ {Θ Γ A} {t : Term Θ Γ A}
                           → ⊢ Θ ⊕ Γ ∥ [ rename-ctx-empty-r {Θ = Θ} ]ʳ ([ rename-ctx-empty-inv {Θ = Θ} ]ʳ t) ≈ t ⦂ A
  empty-ctx-rename-inv-r {t = tm-var x} = eq-refl
  empty-ctx-rename-inv-r {t = tm-meta M ts} = eq-congr-mv λ i → empty-ctx-rename-inv-r
  empty-ctx-rename-inv-r {t = tm-oper f es} = eq-congr λ i → {!!}

  ≈empty-ctx-rename : ∀ {Θ Γ A} {t s : Term Θ (Γ ,, ctx-empty) A} →
                      ⊢ Θ ⊕ Γ ∥ [ rename-ctx-empty-r {Θ = Θ} ]ʳ t ≈ [ rename-ctx-empty-r {Θ = Θ} ]ʳ s ⦂ A
                      → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ t ≈ s ⦂ A
  ≈empty-ctx-rename p = eq-trans
                          (eq-symm empty-ctx-rename-inv-l)
                          (eq-trans
                            (≈empty-ctx-rename-inv p)
                            empty-ctx-rename-inv-l)




  ≈tm-r∘M-aux : ∀ {ψ Ω Γ Δ A} {μ : Ω ⇒M ψ ⊕ Γ} (t : Term ψ (Δ ,, ctx-empty) A)
                → ⊢ Ω ⊕ (Γ ,, Δ) ∥ (([ rename-ctx-empty-r {Θ = ψ} ]ʳ (t)) [ μ ]M) ≈ ([ rename-ctx-empty-r {Θ = Ω} ]ʳ term-reassoc (t [ μ ]M)) ⦂ A
  ≈tm-r∘M-aux (tm-var (var-inl x)) = eq-refl
  ≈tm-r∘M-aux {μ = μ} (SecondOrderSignature.Signature.tm-meta M ts) = {!!}
  ≈tm-r∘M-aux (SecondOrderSignature.Signature.tm-oper f es) = eq-congr λ i → {!!}

  ≈tm-r∘M : ∀ {Θ ψ Ω Γ Δ A} {t : Term Θ ctx-empty A} {ι : ψ ⇒M Θ ⊕ Δ} {μ : Ω ⇒M ψ ⊕ Γ}
            → ⊢ Ω ⊕ (Γ ,, Δ)∥ (([ (rename-ctx-empty-r {Θ = ψ}) ]ʳ (t [ ι ]M)) [ μ ]M) ≈ [ (rename-ctx-empty-r {Θ = Ω}) ]ʳ (t [ μ ∘M ι ]M) ⦂ A
  ≈tm-r∘M {Θ = Θ} {ψ = ψ} {Ω = Ω} {t = t} {ι = ι} {μ = μ} = (eq-trans (≈tm-r∘M-aux {μ = μ} (t [ ι ]M ))  (≈tm-rename (∘M-≈ {t = t} {ι = μ} {μ = ι})))


  ≈tm-mv-inst eq-refl = eq-refl
  ≈tm-mv-inst (eq-symm p) = eq-symm (≈tm-mv-inst p)
  ≈tm-mv-inst (eq-trans p₁ p₂) = eq-trans (≈tm-mv-inst p₁) (≈tm-mv-inst p₂)
  ≈tm-mv-inst (eq-congr ps) = eq-congr λ i → ≈tm-rename (≈tm-mv-inst (ps i))
  ≈tm-mv-inst {μ = μ} (eq-congr-mv {M = M} {xs = xs} {ys = ys} ps) = subst-congr {t = μ M} ([]M-mv-≈ M xs ys μ ps)
  ≈tm-mv-inst {μ = μ} (eq-axiom ε ι) =  eq-trans (≈tm-r∘M {t = ax-lhs ε})
                                                 (eq-symm
                                                   (eq-trans (≈tm-r∘M {t =  ax-rhs ε})
                                                   (≈tm-rename (eq-symm (≈empty-ctx-rename (eq-axiom ε (μ ∘M ι)))))))



  id-action-mv {a = tm-var x} = eq-refl
  id-action-mv {a = tm-meta M ts} = eq-congr-mv λ i → id-action-mv
  id-action-mv {a = tm-oper f es} = eq-congr λ i → id-action-mv-aux
    where
      id-action-mv-aux : ∀ {Θ Γ Δ A} {t : Term Θ (Γ ,, Δ) A} →
                         ⊢ Θ ⊕ ((ctx-empty ,, Γ) ,, Δ) ∥ [ (extendʳ {Θ = Θ} var-inr) ]ʳ t ≈ [ (rename-assoc-l {Θ = Θ}) ]ʳ (t [ id-M ]M) ⦂ A
      id-action-mv-aux {t = tm-var (var-inl x)} = eq-refl
      id-action-mv-aux {t = tm-var (var-inr x)} = eq-refl
      id-action-mv-aux {t = tm-meta M ts} = eq-congr-mv λ i → id-action-mv-aux
      id-action-mv-aux {t = tm-oper f es} = eq-congr λ i → {!id-action-mv-aux!}


  -- tm-reassoc-[]M :  ∀ {Θ ψ Ω Γ Δ Ξ A} {t : Term Θ Ξ A} (ι : ψ ⇒M Θ ⊕ (Δ ,, Γ)) → Ω ⇒M ψ ⊕ Δ → ψ ⇒M Θ ⊕ Γ → (Ω ⇒M Θ ⊕ (Δ ,, Γ)) → ⊢ ψ ⊕ ((Δ ,, Γ) ,, Ξ) ∥ t [ (λ M → term-reassoc (ι M))]M ≈ term-reassoc (t [ ι ]M) ⦂ A
  -- tm-reassoc-[]M = ?

  ∘M-≈ {t = tm-var x} = eq-refl
  ∘M-≈ {t = tm-meta M ts} = {!!} -- subst-congr {!!}
  ∘M-≈ {t = tm-oper f es} = eq-congr λ i → {!!} -- needs an auxiliary function


  -- B.
  term-reassoc-≈ p = {!p!}

  -- the lhs and rhs of an equation are equal
  ind-M-invˡ : ∀ {Θ Γ A} {t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ [ id-M-inv {Θ = Θ} ]ʳ (t [ id-M ]M) ≈ t ⦂ A
  ind-M-invˡ {t = tm-var x} = eq-refl
  ind-M-invˡ {t = SecondOrderSignature.Signature.tm-meta M ts} = eq-congr-mv λ i → ind-M-invˡ
  ind-M-invˡ {t = SecondOrderSignature.Signature.tm-oper f es} = eq-congr {!!}

  eq-axiom-id-aux : ∀ {Θ Γ A} {s t : Term Θ Γ A} → ⊢ Θ ⊕ (ctx-empty ,, Γ) ∥ s [ id-M ]M ≈ t [ id-M ]M ⦂ A → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A
  eq-axiom-id-aux p = eq-trans (eq-symm ind-M-invˡ) (eq-trans (≈tm-rename p) ind-M-invˡ)

  eq-axiom-id : ∀ (ε : ax) → ⊢ ((ax-mv-ctx ε) ⊕ ctx-empty ∥ ax-lhs ε ≈ ax-rhs ε ⦂  (ax-sort ε))
  eq-axiom-id ε = eq-axiom-id-aux (≈empty-ctx-rename (eq-axiom ε id-M))
