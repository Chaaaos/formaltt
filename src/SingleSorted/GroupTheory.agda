open import Agda.Primitive using (lzero; lsuc)
open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as SetoidR

module SingleSorted.GroupTheory where

open import SingleSorted.AlgebraicTheory
open import SingleSorted.Substitution
open import SingleSorted.Group

open Theory 𝒢

e-left-eq : (ctx 1) ⊢ e' ∗ (tm-var (var-inr var-var)) ≈ (tm-var (var-inr var-var))
e-left-eq = eq-axiom-id e-left

sub : ∀ {Γ : Context} (t : Term Γ)
  ----------------
  → Γ ⇒s (ctx 1)
  
sub t = λ{ x → t }

-- Lemma:
lema1 : ∀ {Γ : Context} {t : Term Γ}
  --------------------------------------------
  → (tm-var (var-inr var-var)) [ sub t ]s ≡ t
-- proof  
lema1 = refl

lema2 : ∀ {Γ : Context} {t : Term Γ}
  --------------------------------
  → e' [ sub t ]s ≡ e'
lema2 {Γ} {tm-var x} = {!!}
lema2 {Γ} {Signature.tm-oper f x} = {!!}

-- Lemma: 
-- temp2 : ∀ {Γ : Context} {t : Term Γ} → e' ∗ t ≡ (e' ∗ (tm-var (var-inr var-var))) [ sub t ]s
-- -- proof:
-- temp2 = {!!}

-- -- Lemma:
-- temp3 : ∀ {Γ : Context} {t : Term Γ}
--   → Γ ⊢ (e' ∗ (tm-var (var-inr var-var))) [ sub t ]s ≈ (tm-var (var-inr var-var)) [ sub t ]s
-- -- proof  
-- temp3 {Γ} {t} = eq-subst 𝒢 e-left-eq

-- -- Lemma:
-- temp4 : ∀ {Γ : Context} {t : Term Γ}
--   → Γ ⊢ (tm-var (var-inr var-var)) [ sub t ]s ≈ t
-- -- proof
-- temp4 = ≡-⊢-≈ temp

-- -- Lemma:
-- temp5 : ∀ {Γ : Context} {t : Term Γ}
--   → Γ ⊢ e' ∗ t ≈ (e' ∗ (tm-var (var-inr var-var))) [ sub t ]s
-- -- proof:
-- temp5 = ≡-⊢-≈ temp2


-- Idea of proof: e-left-eq -> apply sub t -> temp3 -> apply temp4 to RHS; apply temp5 to LHS

-- e-left-eq-general : ∀ {Γ : Context} {t : Term Γ} → Γ ⊢ e' ∗ t ≈ t
-- e-left-eq-general {Γ} {t} = eq-tran temp5 {!!}

unique-var : ∀ (x : var (ctx 1)) → x ≡ (var-inr var-var)
unique-var (var-inr var-var) = refl

expansion : ∀ {Γ : Context} (x : Term (ctx 1)) → (ctx 1) ⊢ e' ≈ x ⁱ ∗ x
expansion {Γ} (tm-var x) = eq-symm ( {!!})
expansion {Γ} (tm-oper f x) = eq-symm ( {!!})

-- e-left-eq : (ctx 1) ⊢ e' ∗ (tm-var (var-inr var-var)) ≈ (tm-var (var-inr var-var))
-- e-left-eq = eq-axiom-id e-left

-- e-left-eq-general : ∀ {Γ : Context} {x : Term Γ} → Γ ⊢ e' ∗ x ≈ x
-- e-left-eq-general {Γ} {x} = {!!}


-- unique-var : ∀ (x : var (ctx 1)) → x ≡ (var-inr var-var)
-- unique-var (var-inr var-var) = refl

-- expansion : ∀ {Γ : Context} (x : Term (ctx 1)) → (ctx 1) ⊢ e' ≈ x ⁱ ∗ x
-- expansion {Γ} (tm-var x) = eq-symm ( {!!})
-- expansion {Γ} (tm-oper f x) = eq-symm ( {!!})
