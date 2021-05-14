--{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc; _⊔_; Level)
open import Relation.Unary hiding (_∈_)
open import Data.Empty.Polymorphic
open import Data.List
open import Function.Base
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import SecondOrder.Arity
import Relation.Binary.Reasoning.Setoid as SetoidR

import SecondOrder.Substitution
import SecondOrder.SecondOrderSignature as SecondOrderSignature
import SecondOrder.SecondOrderTheory as SecondOrderTheory

module SecondOrder.MetaTheoremR {ℓ ℓs ℓo ℓa : Level}
                               {𝔸 : Arity}
                               {Σ : SecondOrderSignature.Signature {ℓs} {ℓo} {ℓa} 𝔸}
                               {T : SecondOrderTheory.Theory {ℓs} {ℓo} {ℓa} {𝔸} {Σ} ℓ} where

  open SecondOrderSignature {ℓs} {ℓo} {ℓa} 𝔸
  open Signature Σ
  open SecondOrder.Substitution {ℓs} {ℓo} {ℓa} {𝔸} {Σ}
  open SecondOrderTheory {ℓs} {ℓo} {ℓa} {𝔸} {Σ}
  open Theory {ℓ} T


  --===================================================================================================
  --∥                                    ====================                                         ∥
  --∥                                    ∥  ** Theorems **  ∥                                         ∥
  --∥                                    ====================                                         ∥
  --===================================================================================================

  --===================================================================================================

  ---------------------
  -- A. Main theorems |
  ---------------------

  -- renamings preserve equality of terms
  r-congr : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Θ ⊕ Γ ⇒ʳ Δ}
    → _≈ʳ_ {Θ = Θ} σ τ
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

  -- weakening preserves equality of substitutions
  ≈ˢ-⇑ʳ : ∀ {Θ Γ Δ Ξ A} {σ τ : Θ ⊕ Δ ⇒ˢ Γ} {x : A ∈ Γ}
    → σ ≈ˢ τ
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ ⇑ʳ (σ x) ≈ ⇑ʳ (τ x) ⦂ A
  -- extension preserves equality of renamings
  ≈ʳ-extendʳ : ∀ {Θ : MetaContext} {Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒ʳ Δ}
    → σ ≈ʳ τ
    → _≈ʳ_ {Γ ,, Ξ} {Δ ,, Ξ} (extendʳ {Θ} {Γ} {Δ} σ) (extendʳ {Θ} {Γ} {Δ} τ)
  ≈ʳ-extendʳ {Θ} {Γ} {Δ} {Ξ} {σ = σ} {τ = τ} p (var-inl x) = ≈tm-rename {ρ = var-inl} (p x)
  ≈ʳ-extendʳ p (var-inr x) = eq-refl

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


  extend-r² : ∀ {Θ Γ Δ Ξ Λ A} {t : Term Θ (Γ ,, Ξ ,, Λ) A} {ρ : Θ ⊕ Γ ⇒r Δ }
              → ⊢ Θ ⊕ (Δ ,, Ξ ,, Λ) ∥ [ extend-r {Θ = Θ} (extend-r {Θ = Θ} ρ) ]r t ≈ term-reassoc ([ extend-r {Θ = Θ} {Γ = Γ} ρ ]r ([ rename-assoc-r {Θ = Θ} ]r t)) ⦂ A
  extend-r² = {!!}


  -- Lemma
  empty-ctx-rename-invˡ : ∀ {Θ Γ A} {t : Term Θ (Γ ,, ctx-empty) A}
                           → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ [ rename-ctx-empty-inv {Θ = Θ} ]r ([ rename-ctx-empty-r {Θ = Θ} ]r t) ≈ t ⦂ A

  -- Lemma
  extend-empty-ctx-renameˡ : ∀ {Θ Γ Δ A} {t : Term Θ ((Γ ,, ctx-empty) ,, Δ) A}
    → ⊢ Θ ⊕ ((Γ ,, ctx-empty) ,, Δ) ∥
      ([ extend-r {Θ = Θ} (rename-ctx-empty-inv {Θ = Θ}) ]r ([ extend-r {Θ = Θ} (rename-ctx-empty-r {Θ = Θ})]r t)) ≈ t ⦂ A

  -- Proof
  extend-empty-ctx-renameˡ {Θ = Θ} {Γ = Γ} {Δ = Δ} {A} {t = tm-var (var-inl x)} =
    let open SetoidR (eq-setoid (((Γ ,, ctx-empty) ,, Δ)) Θ A) in
      begin
        ([ extend-r {Θ} (rename-ctx-empty-inv {Θ = Θ}) ]r ([ extend-r {Θ} rename-ctx-empty-r ]r tm-var (var-inl x)))
          ≈⟨ (extend-∘r {t = tm-var x} {ρ = rename-ctx-empty-r} {ν = rename-ctx-empty-inv {Θ = Θ}}) ⟩
        ([ extend-r {Θ} (_∘r_ {Θ = Θ} var-inl rename-ctx-empty-r) ]r weakenˡ (tm-var x))
          ≈⟨ ((extend-weaken {σ = _∘r_ {Θ = Θ} (rename-ctx-empty-inv {Θ = Θ}) (rename-ctx-empty-r {Θ = Θ})} {t = tm-var x})) ⟩
        ([ var-inl ]r ([ rename-ctx-empty-inv {Θ}  ]r ([ rename-ctx-empty-r ]r tm-var x)))
          ≈⟨ (≈tm-rename {t = tm-var x} {ρ = var-inl} empty-ctx-rename-invˡ) ⟩
        (tm-var (var-inl x))
      ∎

  -- Proof
  extend-empty-ctx-renameˡ {t = tm-var (var-inr x)} = eq-refl
  extend-empty-ctx-renameˡ {t = tm-meta M ts} = eq-congr-mv λ i → extend-empty-ctx-renameˡ
  extend-empty-ctx-renameˡ {Θ = Θ} {Γ = Γ} {Δ = Δ} {A} {t = tm-oper f es} =
    eq-congr λ i → {!!}
        
                                                                 -- eq-trans
                                                                 --   (≈tm-rename extend-r²)
                                                                 --   (eq-trans
                                                                 --     (r-congr λ x → extend-r²)
                                                                 --     (eq-trans
                                                                 --       {!!}
                                                                 --       ({!!})))
                                                         -- eq-trans (extend-∘r')
                                                         -- (eq-trans
                                                         --   (eq-symm (r-congr (≈r-extend-r λ x → (∘r-≈ {Θ = Θ} {σ = extend-r rename-ctx-empty-r} {τ = extend-r (rename-ctx-empty-inv {Θ = Θ})}))))
                                                         --   (eq-trans {!extend-r²!} {!!}))

  empty-ctx-rename-invˡ {t = tm-var (var-inl x)} = eq-refl
  empty-ctx-rename-invˡ {t = tm-meta M ts} = eq-congr-mv λ i → empty-ctx-rename-invˡ
  empty-ctx-rename-invˡ {t = tm-oper f es} = eq-congr λ i → extend-empty-ctx-renameˡ


  --==================================================================================================
  --∥                                    ====================                                        ∥
  --∥                                    ∥   ** Proofs **   ∥                                        ∥
  --∥                                    ====================                                        ∥
  --==================================================================================================

  ------------------------------------------------------------------------------------------------------
  -- A.
  r-congr {t = tm-var x} p = p x
  r-congr {t = tm-meta M ts} p = eq-meta λ i → r-congr p
  r-congr {t = tm-oper f es} p = eq-oper λ i → r-congr (≈ʳ-extendʳ p)

  ≈tm-rename eq-refl = eq-refl
  ≈tm-rename (eq-symm p) = eq-symm (≈tm-rename p)
  ≈tm-rename (eq-trans p₁ p₂) = eq-trans (≈tm-rename p₁) (≈tm-rename p₂)
  ≈tm-rename (eq-oper p) = eq-oper λ i → ≈tm-rename (p i)
  ≈tm-rename (eq-meta p) = eq-meta λ i → ≈tm-rename (p i)
  ≈tm-rename {ρ = ρ} (eq-axiom ε I) = {!!} -- I have no idea how one could solve this for the moment

  ∘ʳ-≈ {t = tm-var x} = eq-refl
  ∘ʳ-≈ {t = tm-meta M ts} = eq-meta λ i → ∘ʳ-≈
  ∘ʳ-≈ {t = tm-oper f es} = eq-oper λ i → {!!} -- needs an auxialiary function

  id-action-r {a = tm-var x} = eq-refl
  id-action-r {a = tm-meta M ts} = eq-meta λ i → id-action-r
  id-action-r {a = tm-oper f es} = eq-oper λ i → eq-trans id-action-r-aux (eq-symm (r-congr λ x → idʳ-extend))

  -- B.
  ≈ˢ-⇑ʳ {x = x} p = ≈tm-rename (p x)

  extend-var-inl (tm-var (var-inl x)) τ = {!eq-refl!}
  extend-var-inl (tm-var (var-inr x)) τ = {!!}
  extend-var-inl (tm-meta M ts) τ = {!!}
  extend-var-inl (tm-oper f es) τ = {!!}

  id-action-r-aux = id-action-r

  idʳ-extend {a = var-inl a} = eq-refl
  idʳ-extend {a = var-inr a} = eq-refl
