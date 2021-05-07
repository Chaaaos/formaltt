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
import SecondOrder.MetaTheoremS as MetaTheoremS
import SecondOrder.MetaTheoremR as MetaTheoremR

module SecondOrder.MetaTheoremMI {ℓ ℓs ℓo ℓa : Level}
                               {𝔸 : Arity}
                               {Σ : SecondOrderSignature.Signature {ℓs} {ℓo} {ℓa} 𝔸}
                               {T : SecondOrderTheory.Theory {ℓs} {ℓo} {ℓa} {𝔸} {Σ} ℓ} where

  open SecondOrderSignature {ℓs} {ℓo} {ℓa} 𝔸
  open Signature Σ
  open SecondOrder.Substitution {ℓs} {ℓo} {ℓa} {𝔸} {Σ}
  open SecondOrderTheory {ℓs} {ℓo} {ℓa} {𝔸} {Σ}
  open Theory {ℓ} T
  open MetaTheoremS
  open MetaTheoremR


  --===================================================================================================
  --∥                                    ====================                                         ∥
  --∥                                    ∥  ** Theorems **  ∥                                         ∥
  --∥                                    ====================                                         ∥
  --===================================================================================================

  --===================================================================================================

  ------------------
  -- A. Main Theorems |
  ------------------

  -- actions of equal metavariable instantiations are pointwise equal
  mv-inst-congr : ∀ {Θ ψ Γ Δ A} {t : Term Θ Δ A} {I μ : ψ ⇒ⁱ Θ ⊕ Γ}
                  → I ≈M μ → ⊢ ψ ⊕ (Γ ,, Δ) ∥ t [ I ]ⁱ ≈ t [ μ ]ⁱ ⦂ A

  -- action of a metavariable instantiation preserves equality of terms
  ≈tm-mv-inst : ∀ {Θ ψ Γ Δ A} {s t : Term Θ Δ A} {μ : ψ ⇒ⁱ Θ ⊕ Γ}
                → ⊢ Θ ⊕ Δ ∥ s ≈ t ⦂ A
                → ⊢ ψ ⊕ (Γ ,, Δ) ∥ s [ μ ]ⁱ ≈ t [ μ ]ⁱ ⦂ A

  -- action of metavariable instantiations "commutes" with composition
  ∘ⁱ-≈ : ∀ {Θ ψ Ω Γ Δ Ξ A} {t : Term Θ Γ A} {I : Ω ⇒ⁱ ψ ⊕ Ξ } {μ : ψ ⇒ⁱ Θ ⊕ Δ}
         → ⊢ Ω ⊕ ((Ξ ,, Δ) ,, Γ) ∥ term-reassoc ((t [ μ ]ⁱ) [ I ]ⁱ) ≈ (t [ I ∘ⁱ μ ]ⁱ) ⦂ A

  -- action of the identity metavariable is the identity
  id-action-mv : ∀ {Θ Γ A} {a : Term Θ Γ A}
                 → (⊢ Θ ⊕ (ctx-empty ,, Γ) ∥ weakenʳ a ≈ (a [ idⁱ ]ⁱ) ⦂ A)

  -----------
  -- B. Lemmas /
  -----------

  []ⁱ-mv-≈ : ∀ {Θ ψ Γ Δ} (M : mv Θ) (xs ys : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)
             (I : ψ ⇒ⁱ Θ ⊕ Δ) → (∀ {B} (i : mv-arg Θ M B) → ⊢ Θ ⊕ Γ ∥ xs i ≈ ys i ⦂ B )
             → []ⁱ-mv M xs I ≈s []ⁱ-mv M ys I
  []ⁱ-mv-≈ M xs ys I ps (var-inl x) = eq-refl
  []ⁱ-mv-≈ M xs ys I ps (var-inr x) = ≈tm-mv-inst (ps x)



  term-reassoc-≈ : ∀ {Θ Δ Γ Ξ A} {s t : Term Θ (Γ ,, (Δ ,, Ξ)) A}
                   → ⊢ Θ ⊕ ((Γ ,, Δ) ,, Ξ) ∥ term-reassoc s ≈ term-reassoc t ⦂ A
                   → ⊢ Θ ⊕ (Γ ,, (Δ ,, Ξ)) ∥ s ≈ t ⦂ A
  []ⁱ-mv-congr : ∀ {Θ ψ Γ Δ A} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)
                 (I μ : ψ ⇒ⁱ Θ ⊕ Δ) (x : A ∈ (Δ ,, mv-arity Θ M))
                 → I ≈M μ → ⊢ ψ ⊕ (Δ ,, Γ) ∥ []ⁱ-mv M ts I x ≈ []ⁱ-mv M ts μ x ⦂ A
  []ⁱ-mv-congr M ts I μ (var-inl x) p = eq-refl
  []ⁱ-mv-congr M ts I μ (var-inr x) p = mv-inst-congr {t = ts x} p


  ≈empty-ctx-rename-inv : ∀ {Θ Γ A} {t s : Term Θ Γ A}
                          → ⊢ Θ ⊕ Γ ∥ t ≈ s ⦂ A
                          → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ [ rename-ctx-empty-inv {Θ = Θ} ]ʳ t ≈ [ rename-ctx-empty-inv {Θ = Θ} ]ʳ s ⦂ A
  ≈empty-ctx-rename-inv = ≈tm-rename
  empty-ctx-rename-inv-l : ∀ {Θ Γ A} {t : Term Θ (Γ ,, ctx-empty) A}
                           → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ [ rename-ctx-empty-inv {Θ = Θ} ]ʳ ([ rename-ctx-empty-r {Θ = Θ} ]ʳ t) ≈ t ⦂ A
  empty-ctx-rename-inv-l {t = tm-var (var-inl x)} = eq-refl
  empty-ctx-rename-inv-l {t = tm-meta M ts} = eq-meta λ i → empty-ctx-rename-inv-l
  empty-ctx-rename-inv-l {t = tm-oper f es} = eq-oper λ i → {!!}

  empty-ctx-rename-inv-r : ∀ {Θ Γ A} {t : Term Θ Γ A}
                           → ⊢ Θ ⊕ Γ ∥ [ rename-ctx-empty-r {Θ = Θ} ]ʳ ([ rename-ctx-empty-inv {Θ = Θ} ]ʳ t) ≈ t ⦂ A
  empty-ctx-rename-inv-r {t = tm-var x} = eq-refl
  empty-ctx-rename-inv-r {t = tm-meta M ts} = eq-meta λ i → empty-ctx-rename-inv-r
  empty-ctx-rename-inv-r {t = tm-oper f es} = eq-oper λ i → {!!}

  ≈tm-r∘ⁱ-aux : ∀ {ψ Ω Γ Δ A} {μ : Ω ⇒ⁱ ψ ⊕ Γ} (t : Term ψ (Δ ,, ctx-empty) A)
                → ⊢ Ω ⊕ (Γ ,, Δ) ∥ (([ rename-ctx-empty-r {Θ = ψ} ]ʳ (t)) [ μ ]ⁱ) ≈ ([ rename-ctx-empty-r {Θ = Ω} ]ʳ term-reassoc (t [ μ ]ⁱ)) ⦂ A
  ≈tm-r∘ⁱ-aux (tm-var (var-inl x)) = eq-refl
  ≈tm-r∘ⁱ-aux {μ = μ} (SecondOrderSignature.Signature.tm-meta M ts) = {!!}
  ≈tm-r∘ⁱ-aux (SecondOrderSignature.Signature.tm-oper f es) = eq-oper λ i → {!!}

  ≈tm-r∘ⁱ : ∀ {Θ ψ Ω Γ Δ A} {t : Term Θ ctx-empty A} {I : ψ ⇒ⁱ Θ ⊕ Δ} {μ : Ω ⇒ⁱ ψ ⊕ Γ}
            → ⊢ Ω ⊕ (Γ ,, Δ)∥ (([ (rename-ctx-empty-r {Θ = ψ}) ]ʳ (t [ I ]ⁱ)) [ μ ]ⁱ) ≈ [ (rename-ctx-empty-r {Θ = Ω}) ]ʳ (t [ μ ∘ⁱ I ]ⁱ) ⦂ A
  ≈tm-r∘ⁱ {Θ = Θ} {ψ = ψ} {Ω = Ω} {t = t} {I = I} {μ = μ} = (eq-trans (≈tm-r∘ⁱ-aux {μ = μ} (t [ I ]ⁱ ))  (≈tm-rename (∘ⁱ-≈ {t = t} {I = μ} {μ = I})))




  -- mv-inst-congr-mv : ∀ {Θ ψ Γ Δ A} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)  (I μ : ψ ⇒ⁱ Θ ⊕ Δ) (x : A ∈ (Δ ,, mv-arity Θ M))  → I ≈M μ → ⊢ ψ ⊕ (Δ ,, Γ) ∥ mv-subst-mv {A = A} M ts I x ≈ mv-subst-mv {A = A} M ts μ x ⦂ A

  --==================================================================================================
  --∥                                    ====================                                        ∥
  --∥                                    ∥   ** Proofs **   ∥                                        ∥
  --∥                                    ====================                                        ∥
  --==================================================================================================

  -------------------------------------------------------------------------------------------


  -- IV.
  -- A.

  mv-inst-congr {t = tm-var x} p = eq-refl
  mv-inst-congr {t = tm-meta M ts} {I = I} {μ = μ} p = subst-congr₂ (p M) λ x → []ⁱ-mv-congr M ts I μ x p
  mv-inst-congr {t = tm-oper f es} p = eq-oper λ i → ≈tm-rename (mv-inst-congr {t = es i} p)


  ≈empty-ctx-rename : ∀ {Θ Γ A} {t s : Term Θ (Γ ,, ctx-empty) A} →
                      ⊢ Θ ⊕ Γ ∥ [ rename-ctx-empty-r {Θ = Θ} ]ʳ t ≈ [ rename-ctx-empty-r {Θ = Θ} ]ʳ s ⦂ A
                      → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ t ≈ s ⦂ A
  ≈empty-ctx-rename p = eq-trans
                          (eq-symm empty-ctx-rename-inv-l)
                          (eq-trans
                            (≈empty-ctx-rename-inv p)
                            empty-ctx-rename-inv-l)



  ≈tm-mv-inst eq-refl = eq-refl
  ≈tm-mv-inst (eq-symm p) = eq-symm (≈tm-mv-inst p)
  ≈tm-mv-inst (eq-trans p₁ p₂) = eq-trans (≈tm-mv-inst p₁) (≈tm-mv-inst p₂)
  ≈tm-mv-inst (eq-oper ps) = eq-oper λ i → ≈tm-rename (≈tm-mv-inst (ps i))
  ≈tm-mv-inst {μ = μ} (eq-meta {M = M} {xs = xs} {ys = ys} ps) = subst-congr {t = μ M} ([]ⁱ-mv-≈ M xs ys μ ps)
  ≈tm-mv-inst {μ = μ} (eq-axiom ε I) =  eq-trans (≈tm-r∘ⁱ {t = ax-lhs ε})
                                                 (eq-symm
                                                   (eq-trans (≈tm-r∘ⁱ {t =  ax-rhs ε})
                                                   (≈tm-rename (eq-symm (≈empty-ctx-rename (eq-axiom ε (μ ∘ⁱ I)))))))



  id-action-mv {a = tm-var x} = eq-refl
  id-action-mv {a = tm-meta M ts} = eq-meta λ i → id-action-mv
  id-action-mv {a = tm-oper f es} = eq-oper λ i → id-action-mv-aux
    where
      id-action-mv-aux : ∀ {Θ Γ Δ A} {t : Term Θ (Γ ,, Δ) A} →
                         ⊢ Θ ⊕ ((ctx-empty ,, Γ) ,, Δ) ∥ [ (extendʳ {Θ = Θ} var-inr) ]ʳ t ≈ [ (rename-assoc-l {Θ = Θ}) ]ʳ (t [ idⁱ ]ⁱ) ⦂ A
      id-action-mv-aux {t = tm-var (var-inl x)} = eq-refl
      id-action-mv-aux {t = tm-var (var-inr x)} = eq-refl
      id-action-mv-aux {t = tm-meta M ts} = eq-meta λ i → id-action-mv-aux
      id-action-mv-aux {t = tm-oper f es} = eq-oper λ i → {!id-action-mv-aux!}


  -- tm-reassoc-[]ⁱ :  ∀ {Θ ψ Ω Γ Δ Ξ A} {t : Term Θ Ξ A} (I : ψ ⇒ⁱ Θ ⊕ (Δ ,, Γ)) → Ω ⇒ⁱ ψ ⊕ Δ → ψ ⇒ⁱ Θ ⊕ Γ → (Ω ⇒ⁱ Θ ⊕ (Δ ,, Γ)) → ⊢ ψ ⊕ ((Δ ,, Γ) ,, Ξ) ∥ t [ (λ M → term-reassoc (I M))]ⁱ ≈ term-reassoc (t [ I ]ⁱ) ⦂ A
  -- tm-reassoc-[]ⁱ = ?

  ∘ⁱ-≈ {t = tm-var x} = eq-refl
  ∘ⁱ-≈ {t = tm-meta M ts} = {!!} -- subst-congr {!!}
  ∘ⁱ-≈ {t = tm-oper f es} = eq-oper λ i → {!!} -- needs an auxiliary function


  -- B.
  term-reassoc-≈ p = {!p!}



  --==================================================================================================
  --∥                                    ==========================                                  ∥
  --∥                                    ∥   ** Corollaries **    ∥                                 ∥
  --∥                                    ==========================                                  ∥
  --==================================================================================================



  -- the lhs and rhs of an equation are equal
  ind-M-invˡ : ∀ {Θ Γ A} {t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ [ idⁱ-inv {Θ = Θ} ]ʳ (t [ idⁱ ]ⁱ) ≈ t ⦂ A
  ind-M-invˡ {t = tm-var x} = eq-refl
  ind-M-invˡ {t = SecondOrderSignature.Signature.tm-meta M ts} = eq-meta λ i → ind-M-invˡ
  ind-M-invˡ {t = SecondOrderSignature.Signature.tm-oper f es} = eq-oper {!!}

  eq-axiom-id-aux : ∀ {Θ Γ A} {s t : Term Θ Γ A} → ⊢ Θ ⊕ (ctx-empty ,, Γ) ∥ s [ idⁱ ]ⁱ ≈ t [ idⁱ ]ⁱ ⦂ A → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A
  eq-axiom-id-aux p = eq-trans (eq-symm ind-M-invˡ) (eq-trans (≈tm-rename p) ind-M-invˡ)

  eq-axiom-id : ∀ (ε : ax) → ⊢ ((ax-mv-ctx ε) ⊕ ctx-empty ∥ ax-lhs ε ≈ ax-rhs ε ⦂  (ax-sort ε))
  eq-axiom-id ε = eq-axiom-id-aux (≈empty-ctx-rename (eq-axiom ε idⁱ))
