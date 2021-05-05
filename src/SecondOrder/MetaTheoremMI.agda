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

  -----------
  -- B. Lemmas /
  -----------

  []M-mv-≈ : ∀ {Θ ψ Γ Δ} (M : mv Θ) (xs ys : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)
             (ι : ψ ⇒M Θ ⊕ Δ) → (∀ {B} (i : mv-arg Θ M B) → ⊢ Θ ⊕ Γ ∥ xs i ≈ ys i ⦂ B )
             → []M-mv M xs ι ≈s []M-mv M ys ι
  []M-mv-≈ M xs ys ι ps (var-inl x) = eq-refl
  []M-mv-≈ M xs ys ι ps (var-inr x) = ≈tm-mv-inst (ps x)



  term-reassoc-≈ : ∀ {Θ Δ Γ Ξ A} {s t : Term Θ (Γ ,, (Δ ,, Ξ)) A}
                   → ⊢ Θ ⊕ ((Γ ,, Δ) ,, Ξ) ∥ term-reassoc s ≈ term-reassoc t ⦂ A
                   → ⊢ Θ ⊕ (Γ ,, (Δ ,, Ξ)) ∥ s ≈ t ⦂ A
  []M-mv-congr : ∀ {Θ ψ Γ Δ A} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)
                 (ι μ : ψ ⇒M Θ ⊕ Δ) (x : A ∈ (Δ ,, mv-arity Θ M))
                 → ι ≈M μ → ⊢ ψ ⊕ (Δ ,, Γ) ∥ []M-mv M ts ι x ≈ []M-mv M ts μ x ⦂ A
  []M-mv-congr M ts ι μ (var-inl x) p = eq-refl
  []M-mv-congr M ts ι μ (var-inr x) p = mv-inst-congr {t = ts x} p


  ≈empty-ctx-rename-inv : ∀ {Θ Γ A} {t s : Term Θ Γ A}
                          → ⊢ Θ ⊕ Γ ∥ t ≈ s ⦂ A
                          → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ [ rename-ctx-empty-inv {Θ = Θ} ]r t ≈ [ rename-ctx-empty-inv {Θ = Θ} ]r s ⦂ A
  ≈empty-ctx-rename-inv = ≈tm-rename
  empty-ctx-rename-inv-l : ∀ {Θ Γ A} {t : Term Θ (Γ ,, ctx-empty) A}
                           → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ [ rename-ctx-empty-inv {Θ = Θ} ]r ([ rename-ctx-empty-r {Θ = Θ} ]r t) ≈ t ⦂ A
  empty-ctx-rename-inv-l {t = tm-var (var-inl x)} = eq-refl
  empty-ctx-rename-inv-l {t = tm-meta M ts} = eq-congr-mv λ i → empty-ctx-rename-inv-l
  empty-ctx-rename-inv-l {t = tm-oper f es} = eq-congr λ i → {!!}

  empty-ctx-rename-inv-r : ∀ {Θ Γ A} {t : Term Θ Γ A}
                           → ⊢ Θ ⊕ Γ ∥ [ rename-ctx-empty-r {Θ = Θ} ]r ([ rename-ctx-empty-inv {Θ = Θ} ]r t) ≈ t ⦂ A
  empty-ctx-rename-inv-r {t = tm-var x} = eq-refl
  empty-ctx-rename-inv-r {t = tm-meta M ts} = eq-congr-mv λ i → empty-ctx-rename-inv-r
  empty-ctx-rename-inv-r {t = tm-oper f es} = eq-congr λ i → {!!}

  ≈tm-r∘M-aux : ∀ {ψ Ω Γ Δ A} {μ : Ω ⇒M ψ ⊕ Γ} (t : Term ψ (Δ ,, ctx-empty) A)
                → ⊢ Ω ⊕ (Γ ,, Δ) ∥ (([ rename-ctx-empty-r {Θ = ψ} ]r (t)) [ μ ]M) ≈ ([ rename-ctx-empty-r {Θ = Ω} ]r term-reassoc (t [ μ ]M)) ⦂ A
  ≈tm-r∘M-aux (tm-var (var-inl x)) = eq-refl
  ≈tm-r∘M-aux {μ = μ} (SecondOrderSignature.Signature.tm-meta M ts) = {!!}
  ≈tm-r∘M-aux (SecondOrderSignature.Signature.tm-oper f es) = eq-congr λ i → {!!}

  ≈tm-r∘M : ∀ {Θ ψ Ω Γ Δ A} {t : Term Θ ctx-empty A} {ι : ψ ⇒M Θ ⊕ Δ} {μ : Ω ⇒M ψ ⊕ Γ}
            → ⊢ Ω ⊕ (Γ ,, Δ)∥ (([ (rename-ctx-empty-r {Θ = ψ}) ]r (t [ ι ]M)) [ μ ]M) ≈ [ (rename-ctx-empty-r {Θ = Ω}) ]r (t [ μ ∘M ι ]M) ⦂ A
  ≈tm-r∘M {Θ = Θ} {ψ = ψ} {Ω = Ω} {t = t} {ι = ι} {μ = μ} = (eq-trans (≈tm-r∘M-aux {μ = μ} (t [ ι ]M ))  (≈tm-rename (∘M-≈ {t = t} {ι = μ} {μ = ι})))




  -- mv-inst-congr-mv : ∀ {Θ ψ Γ Δ A} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B)  (ι μ : ψ ⇒M Θ ⊕ Δ) (x : A ∈ (Δ ,, mv-arity Θ M))  → ι ≈M μ → ⊢ ψ ⊕ (Δ ,, Γ) ∥ mv-subst-mv {A = A} M ts ι x ≈ mv-subst-mv {A = A} M ts μ x ⦂ A

  --==================================================================================================
  --∥                                    ====================                                        ∥
  --∥                                    ∥   ** Proofs **   ∥                                        ∥
  --∥                                    ====================                                        ∥
  --==================================================================================================

  -------------------------------------------------------------------------------------------


  -- IV.
  -- A.

  mv-inst-congr {t = tm-var x} p = eq-refl
  mv-inst-congr {t = tm-meta M ts} {ι = ι} {μ = μ} p = subst-congr₂ (p M) λ x → []M-mv-congr M ts ι μ x p
  mv-inst-congr {t = tm-oper f es} p = eq-congr λ i → ≈tm-rename (mv-inst-congr {t = es i} p)


  ≈empty-ctx-rename : ∀ {Θ Γ A} {t s : Term Θ (Γ ,, ctx-empty) A} →
                      ⊢ Θ ⊕ Γ ∥ [ rename-ctx-empty-r {Θ = Θ} ]r t ≈ [ rename-ctx-empty-r {Θ = Θ} ]r s ⦂ A
                      → ⊢ Θ ⊕ (Γ ,, ctx-empty) ∥ t ≈ s ⦂ A
  ≈empty-ctx-rename p = eq-trans
                          (eq-symm empty-ctx-rename-inv-l)
                          (eq-trans
                            (≈empty-ctx-rename-inv p)
                            empty-ctx-rename-inv-l)



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
                         ⊢ Θ ⊕ ((ctx-empty ,, Γ) ,, Δ) ∥ [ (extend-r {Θ = Θ} var-inr) ]r t ≈ [ (rename-assoc-l {Θ = Θ}) ]r (t [ id-M ]M) ⦂ A
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



  --==================================================================================================
  --∥                                    ==========================                                  ∥
  --∥                                    ∥   ** Corollaries **    ∥                                 ∥
  --∥                                    ==========================                                  ∥
  --==================================================================================================



  -- the lhs and rhs of an equation are equal
  ind-M-invˡ : ∀ {Θ Γ A} {t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ [ id-M-inv {Θ = Θ} ]r (t [ id-M ]M) ≈ t ⦂ A
  ind-M-invˡ {t = tm-var x} = eq-refl
  ind-M-invˡ {t = SecondOrderSignature.Signature.tm-meta M ts} = eq-congr-mv λ i → ind-M-invˡ
  ind-M-invˡ {t = SecondOrderSignature.Signature.tm-oper f es} = eq-congr {!!}

  eq-axiom-id-aux : ∀ {Θ Γ A} {s t : Term Θ Γ A} → ⊢ Θ ⊕ (ctx-empty ,, Γ) ∥ s [ id-M ]M ≈ t [ id-M ]M ⦂ A → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A
  eq-axiom-id-aux p = eq-trans (eq-symm ind-M-invˡ) (eq-trans (≈tm-rename p) ind-M-invˡ)

  eq-axiom-id : ∀ (ε : ax) → ⊢ ((ax-mv-ctx ε) ⊕ ctx-empty ∥ ax-lhs ε ≈ ax-rhs ε ⦂  (ax-sort ε))
  eq-axiom-id ε = eq-axiom-id-aux (≈empty-ctx-rename (eq-axiom ε id-M))


