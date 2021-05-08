{-# OPTIONS --allow-unsolved-metas #-}

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
  r-congr : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Θ ⊕ Γ ⇒r Δ}
    → _≈r_ {Θ = Θ} σ τ
    → ⊢ Θ ⊕ Δ ∥ [ σ ]r t ≈ [ τ ]r t ⦂ A

  -- renaming preserves equality of terms
  ≈tm-rename : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Θ ⊕ Γ ⇒r Δ}
    → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A
    → ⊢ Θ ⊕ Δ ∥ [ ρ ]r s ≈ [ ρ ]r t ⦂ A

  -- action of renaming commutes with composition
  ∘r-≈ :  ∀ {Θ Γ Δ Ξ A} {t : Term Θ Γ A} {σ : Θ ⊕ Γ ⇒r Δ} {τ : Θ ⊕ Δ ⇒r Ξ}
    → ⊢ Θ ⊕ Ξ ∥ [ τ ]r ([ σ ]r t) ≈ ([ _∘r_ {Θ = Θ} τ σ ]r t) ⦂ A

  -- action of the identity renaming is the identity
  id-action-r : ∀ {Θ Γ A} {a : Term Θ Γ A} → (⊢ Θ ⊕ Γ ∥ a ≈ ([ (id-r {Θ = Θ}) ]r a) ⦂ A)

  ------------------------------
  -- B. Lemmas and corollaries |
  ------------------------------

  -- weakening preserves equality of substitutions
  ≈s-weakenˡ : ∀ {Θ Γ Δ Ξ A} {σ τ : Θ ⊕ Δ ⇒s Γ} {x : A ∈ Γ}
    → σ ≈s τ
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ weakenˡ (σ x) ≈ weakenˡ (τ x) ⦂ A
  -- extension preserves equality of renamings
  ≈r-extend-r : ∀ {Θ : MetaContext} {Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒r Δ}
    → σ ≈r τ
    → _≈r_ {Γ ,, Ξ} {Δ ,, Ξ} (extend-r {Θ} {Γ} {Δ} σ) (extend-r {Θ} {Γ} {Δ} τ)
  ≈r-extend-r {Θ} {Γ} {Δ} {Ξ} {σ = σ} {τ = τ} p (var-inl x) = ≈tm-rename {ρ = var-inl} (p x)
  ≈r-extend-r p (var-inr x) = eq-refl


  extend-weaken : ∀ {Θ Γ Δ Ξ A} {σ : Θ ⊕ Γ ⇒r Δ} {t : Term Θ Γ A}
    → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ [ extend-r {Θ = Θ} σ ]r (weakenˡ t) ≈ weakenˡ ( [ σ ]r t) ⦂ A
  extend-weaken {t = tm-var x} = eq-refl
  extend-weaken {t = tm-meta M ts} = eq-congr-mv λ i → extend-weaken
  extend-weaken {t = tm-oper f es} = eq-congr (λ i → {!!})


  -- auxiliary function for id-action-r, with extended context
  id-action-r-aux : ∀ {Θ Γ Ξ A} {a : Term Θ (Γ ,, Ξ) A}
    → (⊢ Θ ⊕ (Γ ,, Ξ) ∥ a ≈ ([ (id-r {Θ = Θ}) ]r a) ⦂ A)

  -- auxiliary function : the extension of the identity renaming is the identity
  id-r-extend : ∀ {Θ Γ Ξ A} {a : A ∈ (Γ ,, Ξ)}
    → ⊢ Θ ⊕ (Γ ,, Ξ) ∥
         tm-var (extend-r {Θ} {Γ} {Γ} (id-r {Θ = Θ} {Γ = Γ}) {Ξ} a)
       ≈ tm-var (id-r {Θ = Θ} {Γ = Γ ,, Ξ} a) ⦂ A

  -- extending a composition is like extending each function and then compose
  extend-∘r : ∀ {Θ Γ Δ Ξ Λ A} {t : Term Θ Γ A} {ρ : Θ ⊕ Γ ⇒r Δ} {ν : Θ ⊕ Δ ⇒r Ξ}
              → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ [ extend-r {Θ = Θ} ν ]r ([ extend-r {Θ = Θ} ρ ]r (weakenˡ t)) ≈ [ extend-r {Θ = Θ} ( _∘r_ {Θ = Θ} ν ρ) ]r (weakenˡ t) ⦂ A
  extend-∘r {t = SecondOrderSignature.Signature.tm-var x} = eq-refl
  extend-∘r {t = SecondOrderSignature.Signature.tm-meta M ts} = eq-congr-mv λ i → extend-∘r
  extend-∘r {t = SecondOrderSignature.Signature.tm-oper f es} = eq-congr λ i → {!!}

  extend-∘r' : ∀ {Θ Γ Δ Ξ Λ A} {t : Term Θ (Γ ,, Λ) A} {ρ : Θ ⊕ Γ ⇒r Δ} {ν : Θ ⊕ Δ ⇒r Ξ}
              → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ [ extend-r {Θ = Θ} ν ]r ([ extend-r {Θ = Θ} ρ ]r t) ≈ [ extend-r {Θ = Θ} ( _∘r_ {Θ = Θ} ν ρ) ]r t ⦂ A
  extend-∘r' {t = SecondOrderSignature.Signature.tm-var (var-inl x)} = eq-refl
  extend-∘r' {t = SecondOrderSignature.Signature.tm-var (var-inr x)} = eq-refl
  extend-∘r' {t = SecondOrderSignature.Signature.tm-meta M ts} = eq-congr-mv (λ i → extend-∘r')
  extend-∘r' {t = SecondOrderSignature.Signature.tm-oper f es} = eq-congr (λ i → {!!})

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
  r-congr {t = tm-meta M ts} p = eq-congr-mv λ i → r-congr p
  r-congr {t = tm-oper f es} p = eq-congr λ i → r-congr (≈r-extend-r p)


  r∘M-≈ : ∀ {Θ ψ Γ Δ A} {t : Term Θ ctx-empty A} {ρ : ψ ⊕ Γ ⇒r Δ} {ι : ψ ⇒M Θ ⊕ Γ}
          → ⊢ ψ ⊕ Δ ∥ ([ ρ ]r ([ rename-ctx-empty-r {Θ = ψ} ]r (t [ ι ]M))) ≈ ([ rename-ctx-empty-r {Θ = ψ} ]r (t [ ρ r∘M ι ]M)) ⦂ A
  r∘M-≈ = {!!}


  ≈tm-rename eq-refl = eq-refl
  ≈tm-rename (eq-symm p) = eq-symm (≈tm-rename p)
  ≈tm-rename (eq-trans p₁ p₂) = eq-trans (≈tm-rename p₁) (≈tm-rename p₂)
  ≈tm-rename (eq-congr p) = eq-congr λ i → ≈tm-rename (p i)
  ≈tm-rename (eq-congr-mv p) = eq-congr-mv λ i → ≈tm-rename (p i)
  ≈tm-rename {ρ = ρ} (eq-axiom ε ι) = eq-trans
                                        (r∘M-≈ {t = ax-lhs ε})
                                        (eq-trans
                                          (eq-axiom ε (ρ r∘M ι))
                                          (eq-symm (r∘M-≈ {t = ax-rhs ε})))

  ∘r-≈ {t = tm-var x} = eq-refl
  ∘r-≈ {t = tm-meta M ts} = eq-congr-mv λ i → ∘r-≈
  ∘r-≈ {t = tm-oper f es} = eq-congr λ i → {!!} -- needs an auxialiary function

  id-action-r {a = tm-var x} = eq-refl
  id-action-r {a = tm-meta M ts} = eq-congr-mv λ i → id-action-r
  id-action-r {a = tm-oper f es} = eq-congr λ i → eq-trans id-action-r-aux (eq-symm (r-congr λ x → id-r-extend))

  -- B.
  ≈s-weakenˡ {x = x} p = ≈tm-rename (p x)

  id-action-r-aux = id-action-r

  id-r-extend {a = var-inl a} = eq-refl
  id-r-extend {a = var-inr a} = eq-refl

