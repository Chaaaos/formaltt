open import Agda.Primitive using (lsuc; _⊔_)
open import Data.Fin using (Fin)

open import SingleSorted.AlgebraicTheory

module SingleSorted.Substitution {ℓ} {Σ : Signature} (T : Theory ℓ Σ) where

  open Theory T

  -- an equality is preserved by the action of the identity
  eq-id-action : ∀ {Γ : Context} {u v : Term Γ} → (Γ ⊢ (u [ id-s ]s) ≈ (v [ id-s ]s)) → (Γ ⊢ u ≈ v)
  eq-id-action {u = u} {v = v} p = eq-tran (id-action {a = u}) (eq-tran p (eq-symm (id-action {a = v})))

  -- equality of substitutions
  _≈s_ : ∀ {Γ Δ : Context} → Γ ⇒s Δ → Γ ⇒s Δ → Set (lsuc ℓ)
  _≈s_ {Γ = Γ} σ ρ = ∀ x → Γ ⊢ σ x ≈ ρ x

  infix 5 _≈s_

  -- reflexivity of the equality of substitutions
  refl-subst : ∀ {Γ Δ : Context} {f : Γ ⇒s Δ} → f ≈s f
  refl-subst = λ x → eq-refl

  -- symmetry of the equality of substitutions
  symm-subst : ∀ {Γ Δ : Context} {f g : Γ ⇒s Δ} → f ≈s g → g ≈s f
  symm-subst {Γ} {Δ} {f} {g} p = λ x → eq-symm (p x)

  -- transitivity of the equality of substitutions
  trans-subst : ∀ {Γ Δ : Context} {f g h : Γ ⇒s Δ} → f ≈s g → g ≈s h → f ≈s h
  trans-subst {Γ} {Δ} {f} {g} {h} p q = λ x → eq-tran (p x) (q x)

  -- neutrality of tm-var
  tm-var-id : ∀ {Γ : Context} {x : Term Γ} → Γ ⊢ x [ id-s ]s ≈ x
  tm-var-id {x = tm-var x} = eq-refl
  tm-var-id {x = tm-oper f x} = eq-congr (λ i → tm-var-id)

  -- any two substitutions into the empty context are equal
  empty-ctx-subst-unique : ∀ {Γ : Context} {σ ρ : Γ ⇒s ctx-empty} → σ ≈s ρ
  empty-ctx-subst-unique ()

  -- composition of substitutions is functorial
  subst-∘s : ∀ {Γ Δ Θ} {ρ : Δ ⇒s Γ} {σ : Θ ⇒s Δ} (t : Term Γ) → Θ ⊢ (t [ ρ ]s) [ σ ]s ≈ t [ ρ ∘s σ ]s
  subst-∘s (tm-var x) = eq-refl
  subst-∘s (tm-oper f ts) = eq-congr (λ i → subst-∘s (ts i))

  -- substitution preserves equality
  eq-subst : ∀ {Γ Δ : Context} {σ : Γ ⇒s Δ} {u v : Term Δ} → Δ ⊢ u ≈ v → Γ ⊢ u [ σ ]s ≈ v [ σ ]s
  eq-subst eq-refl = eq-refl
  eq-subst (eq-symm ξ) = eq-symm (eq-subst ξ)
  eq-subst (eq-tran ζ ξ) = eq-tran (eq-subst ζ) (eq-subst ξ)
  eq-subst (eq-congr ξ) = eq-congr (λ i → eq-subst (ξ i))
  eq-subst {σ = σ} (eq-axiom ε ρ) = eq-tran (subst-∘s (eq-lhs ε)) (eq-tran (eq-axiom ε (ρ ∘s σ)) (eq-symm (subst-∘s (eq-rhs ε))))

 -- equivalent substitutions act the same on terms
  equiv-subst : ∀ {Γ Δ : Context} {σ τ : Γ ⇒s Δ} u → σ ≈s τ → Γ ⊢ u [ σ ]s ≈ u [ τ ]s
  equiv-subst (tm-var x) ξ = ξ x
  equiv-subst (tm-oper f ts) ξ = eq-congr (λ i → equiv-subst (ts i) ξ)

 -- equivalent substitution preserve equality
  equiv-eq-subst : ∀ {Γ Δ : Context} {σ τ : Γ ⇒s Δ} {u v : Term Δ} → σ ≈s τ → Δ ⊢ u ≈ v → Γ ⊢ u [ σ ]s ≈ v [ τ ]s
  equiv-eq-subst {u = u} p eq-refl = equiv-subst u p
  equiv-eq-subst p (eq-symm q) = eq-symm  (equiv-eq-subst (symm-subst p) q)
  equiv-eq-subst p (eq-tran q r) = eq-tran (eq-subst q) (equiv-eq-subst p r)
  equiv-eq-subst p (eq-congr ξ) = eq-congr λ i → equiv-eq-subst p (ξ i)
  equiv-eq-subst {σ = σ} {τ = τ} p (eq-axiom ε θ) = eq-tran (eq-subst (eq-axiom ε θ)) (equiv-subst (eq-rhs ε [ θ ]s) p)

  -- the pairing of two substitutions
  ⟨_,_⟩s : ∀ {Γ Δ Θ} (σ : Γ ⇒s Δ) (ρ : Γ ⇒s Θ) → Γ ⇒s (ctx-concat Δ Θ)
  ⟨ σ , ρ ⟩s (var-inl x) = σ x
  ⟨ σ , ρ ⟩s (var-inr y) = ρ y

  -- composition of substitutions preserves equality
  ∘s-resp-≈s : ∀ {Γ Δ Θ} {σ₁ σ₂ : Γ ⇒s Δ} {τ₁ τ₂ : Δ ⇒s Θ} →
               τ₁ ≈s τ₂ → σ₁ ≈s σ₂ → τ₁ ∘s σ₁ ≈s τ₂ ∘s σ₂
  ∘s-resp-≈s ξ ζ z = equiv-eq-subst ζ (ξ z)
