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

  -- ** Theorems **

  -- Renamings
  -- renaming preserves equality of terms
  ≈tm-rename : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : _⇒r_ {Θ} Γ Δ} → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Δ ∥ tm-rename ρ s ≈ tm-rename ρ t ⦂ A
  -- weakening preserves equality of substitutions
  ≈s-weakenˡ : ∀ {Θ Γ Δ Ξ A} {σ τ : Δ ⇒s Γ} {x : A ∈ Γ} → σ ≈s τ → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ weakenˡ (σ x) ≈ weakenˡ (τ x) ⦂ A

  -- Renamings to substitutions

  -- enables to use a renaming as a substitution
  r-to-subst : ∀ {Θ Γ Δ} (ρ : _⇒r_ {Θ} Γ Δ) → _⇒s_ {Θ} Δ Γ
  r-to-subst-extend-sˡ : ∀ {Θ Γ Δ Ξ} {ρ : _⇒r_ {Θ} Γ Δ} →  _≈s_ {Θ = Θ} (r-to-subst (extend-r {Θ = Θ} ρ {Ξ = Ξ})) (extend-sˡ (r-to-subst ρ))
  r-to-subst-≈ :  ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {ρ : _⇒r_ {Θ = Θ} Γ Δ} → ⊢ Θ ⊕ Δ ∥ (tm-rename ρ t) ≈ t [ r-to-subst ρ ]s ⦂ A
  r-to-subst-≈aux : ∀ {Θ Γ Δ Ξ A} {t : Term Θ (Γ ,, Ξ) A} {ρ : _⇒r_ {Θ} Γ Δ} → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ (tm-rename (extend-r {Θ = Θ} ρ) t) ≈ t [ extend-sˡ (r-to-subst ρ) ]s ⦂ A

  -- Substitutions

  -- extension of the identity substitution is the identity substitution
  id-s-extendˡ : ∀ {Θ Γ Ξ A} {a : A ∈ (Γ ,, Ξ)} → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ extend-sˡ {Θ} {Γ} {Γ} {Ξ} (id-s {Γ = Γ}) {A} a ≈  id-s {Γ = Γ ,, Ξ} a ⦂ A
  -- actions of equal substitutions are pointwise equal
  subst-congr : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Δ ⇒s Γ} → σ ≈s τ → ⊢ Θ ⊕ Δ ∥ t [ σ ]s ≈  t [ τ ]s ⦂ A
  subst-congr-aux : ∀ {Θ Γ Δ Ξ A} {t : Term Θ (Γ ,, Ξ) A} {σ τ : Δ ⇒s Γ} → σ ≈s τ → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ t [ extend-sˡ σ ]s ≈  t [ extend-sˡ τ ]s ⦂ A
  -- extension of substitutions preserve composition
  ∘s-extendˡ : ∀ {Θ Γ Δ Ξ Λ} {σ : _⇒s_ {Θ} Δ Ξ} {τ : _⇒s_ {Θ} Γ Δ} → ((extend-sˡ {Γ = Δ} {Δ = Ξ} {Ξ = Λ} σ) ∘s (extend-sˡ τ)) ≈s extend-sˡ {Γ = Γ} {Δ = Ξ} {Ξ = Λ} (σ ∘s τ)
  ∘s-extendˡ-aux : ∀ {Θ Γ Δ Ξ A} {τ : _⇒s_ {Θ} Δ Γ} {t : Term Θ Γ A} → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ tm-rename var-inl t [ extend-sˡ τ ]s ≈ tm-rename var-inl (t [ τ ]s) ⦂ A
  ∘s-≈ :  ∀ {Θ Γ Δ Ξ A} {t : Term Θ Γ A} {σ : _⇒s_ {Θ} Δ Γ} {τ : _⇒s_ {Θ} Ξ Δ} → ⊢ Θ ⊕ Ξ ∥ (t [ σ ]s) [ τ ]s ≈ (t [ σ ∘s τ ]s) ⦂ A
  ∘s-≈aux :  ∀ {Θ Γ Δ Ξ Λ A} {t : Term Θ (Γ ,, Λ) A} {σ : _⇒s_ {Θ} Δ Γ} {τ : _⇒s_ {Θ} Ξ Δ} → ⊢ Θ ⊕ (Ξ ,, Λ) ∥ (t [ extend-sˡ σ ]s) [ extend-sˡ τ ]s ≈ (t [ (extend-sˡ σ) ∘s (extend-sˡ τ) ]s) ⦂ A
  -- extension of substitutions preserves equality of substitutions
  ≈s-extend-sˡ : ∀ {Θ Γ Δ Ξ} {σ τ : Γ ⇒s Δ} → σ ≈s τ → extend-sˡ {Θ} {Γ} {Δ} {Ξ} σ ≈s extend-sˡ {Θ} {Γ} {Δ} {Ξ} τ

  -- Metavariable extensions




  -- ** Proofs **

  id-s-extendˡ {a = var-inl a} = eq-refl
  id-s-extendˡ {a = var-inr a} = eq-refl


  subst-congr {t = Signature.tm-var x} p = p x
  subst-congr {t = Signature.tm-meta M ts} p = eq-congr-mv λ i → subst-congr {t = ts i} p
  subst-congr {t = Signature.tm-oper f es} p = eq-congr λ i → subst-congr-aux {t = es i} p

  ∘s-extendˡ (var-inr x) = eq-refl
  ∘s-extendˡ {Γ = Γ} {Δ = Δ} {Ξ = Ξ} {σ = σ} (var-inl x)  = ∘s-extendˡ-aux {Γ = Δ} {Δ = Γ} {t = σ x}

  ∘s-extendˡ-aux {t = tm-var x} = eq-refl
  ∘s-extendˡ-aux {t = tm-meta M ts} = eq-congr-mv λ i → ∘s-extendˡ-aux {t = ts i}
  ∘s-extendˡ-aux {t = tm-oper f es} = eq-congr λ i → {!!}

  r-to-subst ρ x = tm-var (ρ x)


  r-to-subst-extend-sˡ (var-inl x) = eq-refl
  r-to-subst-extend-sˡ (var-inr x) = eq-refl


  r-to-subst-≈ {t = tm-var x} = eq-refl
  r-to-subst-≈ {t = tm-meta M ts} = eq-congr-mv λ i → r-to-subst-≈
  r-to-subst-≈ {t = tm-oper f es} = eq-congr λ i → r-to-subst-≈aux

  r-to-subst-≈aux {Θ = Θ} {Γ = Γ} {Δ = Δ} {t = t} {ρ = ρ} = eq-trans r-to-subst-≈ (subst-congr {t = t} (r-to-subst-extend-sˡ {ρ = ρ}))


  ∘s-≈ {t = tm-var x} = eq-refl
  ∘s-≈ {t = tm-meta M ts} = eq-congr-mv λ i → ∘s-≈ {t = ts i}
  ∘s-≈ {t = tm-oper f es} {σ = σ} {τ = τ} = eq-congr λ i → eq-trans (∘s-≈aux {t = es i} {σ = σ} {τ = τ}) (subst-congr {t = es i} {σ =  extend-sˡ σ ∘s extend-sˡ τ} {τ = extend-sˡ (σ ∘s τ)} ∘s-extendˡ)

  ∘s-≈aux {Γ = Γ} {Λ = Λ} {t = tm-var x}  {σ = σ} = ∘s-≈ {Γ = (Γ ,, Λ)} {t = tm-var x} {σ = extend-sˡ σ}
  ∘s-≈aux {t = tm-meta M ts} = eq-congr-mv λ i → ∘s-≈aux {t = ts i}
  ∘s-≈aux {t = tm-oper f es} {σ = σ} {τ = τ} = eq-congr λ i → eq-trans (∘s-≈aux {t = es i}) (subst-congr {t = es i} {σ = extend-sˡ (extend-sˡ σ) ∘s extend-sˡ (extend-sˡ τ)} {τ = extend-sˡ (extend-sˡ σ ∘s extend-sˡ τ)} ∘s-extendˡ)

  ≈tm-rename eq-refl = eq-refl
  ≈tm-rename (eq-symm p) = eq-symm (≈tm-rename p)
  ≈tm-rename (eq-trans p₁ p₂) = eq-trans (≈tm-rename p₁) (≈tm-rename p₂)
  ≈tm-rename (eq-congr p) = eq-congr λ i → ≈tm-rename (p i)
  ≈tm-rename (eq-congr-mv p) = eq-congr-mv λ i → ≈tm-rename (p i)
  ≈tm-rename {ρ = ρ} (eq-axiom ε ι) = {!≈tm-rename!} -- I have no idea how one could solve this for the moment

  ≈s-weakenˡ {x = x} p = ≈tm-rename (p x)

  ≈s-extend-sˡ p (var-inl x) = ≈s-weakenˡ p
  ≈s-extend-sˡ p (var-inr x) = eq-refl

  subst-congr-aux {Γ = Γ} {Ξ = Ξ} {t = t} p = subst-congr {Γ = Γ ,, Ξ} {t = t} λ x → ≈s-extend-sˡ p x

  -- the action of the identity substitution is the identity
  id-action : ∀ {Θ Γ A} {a : Term Θ Γ A} → (⊢ Θ ⊕ Γ ∥ a ≈ (a [ id-s ]s) ⦂ A)
  id-action {a = tm-var x} = eq-refl
  id-action {a = tm-meta M ts} = eq-congr-mv λ i → id-action
  id-action {a = tm-oper f es} = eq-congr λ i → eq-trans id-action-aux (eq-symm (subst-congr {t = es i} λ x → id-s-extendˡ))
    where
      id-action-aux : ∀ {Θ Γ Ξ A} {t : Term Θ (Γ ,, Ξ) A} → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ t ≈  (t [ id-s ]s) ⦂ A
      id-action-aux = id-action

  -- the action of the identity metavariable instantiation is the identity
  id-action-mv : ∀ {Θ Γ A} {a : Term Θ Γ A} → (⊢ Θ ⊕ (ctx-empty ,, Γ) ∥ weakenʳ a ≈ (a [ id-M ]M) ⦂ A)
  id-action-mv {a = tm-var x} = eq-refl
  id-action-mv {a = tm-meta M ts} = eq-congr-mv λ i → id-action-mv
  id-action-mv {a = tm-oper f es} = eq-congr λ i → {!!} -- needs an auxiliary function
    -- where
    --   id-action-mv-aux :


  eq-axiom-id-aux : ∀ {Θ Γ A} {s t : Term Θ Γ A} → ⊢ Θ ⊕ (ctx-empty ,, Γ) ∥ weakenʳ s ≈ weakenʳ t ⦂ A → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A
  eq-axiom-id-aux p = {!!}

  eq-axiom-id : ∀ (ε : ax) → ⊢ ((ax-mv-ctx ε) ⊕ ctx-empty ∥ ax-lhs ε ≈ ax-rhs ε ⦂  (ax-sort ε))
  eq-axiom-id ε = eq-axiom-id-aux (eq-trans id-action-mv (eq-symm (eq-trans id-action-mv (eq-symm {!!})))) -- doesn't work, problem with contexts (I am not even sure that it akes sense to try to prove this - maybe some definitions are wrong ?)
