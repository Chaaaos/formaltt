open import Agda.Primitive using (lsuc; _⊔_)
open import Data.Fin using (Fin)

open import MultiSorted.AlgebraicTheory

module MultiSorted.Substitution {ℓ} {𝓈 ℴ} {Σ : Signature {𝓈} {ℴ}} (T : Theory ℓ Σ) where

  open Theory T

  -- an equality is preserved by the action of the identity
  eq-id-action : ∀ {Γ : Context} {A} {u v : Term Γ A} → (⊢ Γ ∥ (u [ id-s ]s) ≈ (v [ id-s ]s) ⦂ A) → (⊢ Γ ∥ u ≈ v ⦂ A)
  eq-id-action {u = u} {v = v} p = eq-tran (id-action {a = u}) (eq-tran p (eq-symm (id-action {a = v})))

  -- equality of substitutions
  _≈s_ : ∀ {Γ Δ : Context} → Γ ⇒s Δ → Γ ⇒s Δ → Set (lsuc (ℓ ⊔ 𝓈 ⊔ ℴ))
  _≈s_ {Γ} {Δ} σ ρ = ∀ x → ⊢ Γ ∥ σ x ≈ ρ x ⦂ sort-of Δ x

  infix 5 _≈s_

  -- reflexivity of the equality of substitutions
  refl-subst : ∀ {γ δ : Context} {f : γ ⇒s δ} → f ≈s f
  refl-subst = λ x → eq-refl

  -- symmetry of the equality of substitutions
  symm-subst : ∀ {Γ Δ : Context} {f g : Γ ⇒s Δ} → f ≈s g → g ≈s f
  symm-subst {Γ} {Δ} {f} {g} p = λ x → eq-symm (p x)

  -- transitivity of the equality of substitutions
  trans-subst : ∀ {Γ Δ : Context} {f g h : Γ ⇒s Δ} → f ≈s g → g ≈s h → f ≈s h
  trans-subst {Γ} {Δ} {f} {g} {h} p q = λ x → eq-tran (p x) (q x)

  -- neutrality of tm-var
  tm-var-id : ∀ {Γ} {A} {t : Term Γ A} → ⊢ Γ ∥ t [ id-s ]s ≈ t ⦂ A
  tm-var-id {t = tm-var x} = eq-refl
  tm-var-id {t = tm-oper f ts} = eq-congr (λ i → tm-var-id)

  -- any two substitutions into the empty context are equal
  empty-ctx-subst-unique : ∀ {Γ : Context} {σ ρ : Γ ⇒s ctx-empty} → σ ≈s ρ
  empty-ctx-subst-unique ()

  -- composition of substitutions is functorial
  subst-∘s : ∀ {Γ Δ Θ} {ρ : Δ ⇒s Γ} {σ : Θ ⇒s Δ} {A} (t : Term Γ A) →
           ⊢ Θ ∥ (t [ ρ ]s) [ σ ]s ≈ t [ ρ ∘s σ ]s ⦂ A
  subst-∘s (tm-var x) = eq-refl
  subst-∘s (tm-oper f ts) = eq-congr (λ i → subst-∘s (ts i))

  -- substitution preserves equality
  eq-subst : ∀ {Γ Δ : Context} {σ : Γ ⇒s Δ} {A} {u v : Term Δ A} →
             ⊢ Δ ∥ u ≈ v ⦂ A → ⊢ Γ ∥ u [ σ ]s ≈ v [ σ ]s ⦂ A
  eq-subst eq-refl = eq-refl
  eq-subst (eq-symm ξ) = eq-symm (eq-subst ξ)
  eq-subst (eq-tran ζ ξ) = eq-tran (eq-subst ζ) (eq-subst ξ)
  eq-subst (eq-congr ξ) = eq-congr (λ i → eq-subst (ξ i))
  eq-subst {σ = σ} (eq-axiom ε ρ) = eq-tran (subst-∘s (ax-lhs ε)) (eq-tran (eq-axiom ε (ρ ∘s σ)) (eq-symm (subst-∘s (ax-rhs ε))))

 -- equivalent substitutions act the same on terms
  equiv-subst : ∀ {Γ Δ : Context} {σ τ : Γ ⇒s Δ} {A} (u : Term Δ A) →
                σ ≈s τ → ⊢ Γ ∥ u [ σ ]s ≈ u [ τ ]s ⦂ A
  equiv-subst (tm-var x) ξ = ξ x
  equiv-subst (tm-oper f ts) ξ = eq-congr (λ i → equiv-subst (ts i) ξ)

 -- equivalent substitution preserve equality
  equiv-eq-subst : ∀ {Γ Δ : Context} {σ τ : Γ ⇒s Δ} {A} {u v : Term Δ A} →
                   σ ≈s τ → ⊢ Δ ∥ u ≈ v ⦂ A → ⊢ Γ ∥ u [ σ ]s ≈ v [ τ ]s ⦂ A
  equiv-eq-subst {u = u} p eq-refl = equiv-subst u p
  equiv-eq-subst p (eq-symm q) = eq-symm  (equiv-eq-subst (symm-subst p) q)
  equiv-eq-subst p (eq-tran q r) = eq-tran (eq-subst q) (equiv-eq-subst p r)
  equiv-eq-subst p (eq-congr ξ) = eq-congr λ i → equiv-eq-subst p (ξ i)
  equiv-eq-subst {σ = σ} {τ = τ} p (eq-axiom ε θ) = eq-tran (eq-subst (eq-axiom ε θ)) (equiv-subst (ax-rhs ε [ θ ]s) p)

  -- the pairing of two substitutions
  ⟨_,_⟩s : ∀ {Γ Δ Θ} (σ : Γ ⇒s Δ) (ρ : Γ ⇒s Θ) → Γ ⇒s ctx-concat Δ Θ
  ⟨ σ , ρ ⟩s (var-inl x) = σ x
  ⟨ σ , ρ ⟩s (var-inr y) = ρ y

  -- composition of substitutions preserves equality
  ∘s-resp-≈s : ∀ {Γ Δ Θ} {σ₁ σ₂ : Γ ⇒s Δ} {τ₁ τ₂ : Δ ⇒s Θ} →
               τ₁ ≈s τ₂ → σ₁ ≈s σ₂ → τ₁ ∘s σ₁ ≈s τ₂ ∘s σ₂
  ∘s-resp-≈s ξ ζ z = equiv-eq-subst ζ (ξ z)

  -- the action of a substitution on an equation
  open Equation
  _[_]s-eq : ∀ (ε : Equation Σ) {Γ : Context} ( σ : Γ ⇒s (eq-ctx ε)) → Equation Σ
  _[_]s-eq ε {Γ} σ = Γ ∥ ((eq-lhs ε) [ σ ]s) ≈ ((eq-rhs ε) [ σ ]s) ⦂ (eq-sort ε)
