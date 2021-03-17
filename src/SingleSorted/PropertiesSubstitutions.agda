open import Agda.Primitive
open import Agda.Builtin.Nat
open import Data.Fin
open import SingleSorted.AlgebraicTheory

module SingleSorted.PropertiesSubstitutions {ℓ : Level} {Σ : Signature} {T : Theory ℓ Σ} where

  open import SingleSorted.AlgebraicTheory public
  open Theory T

  -- the action of the identity substitution is the identity
  id-action : ∀ {Σ : Signature} {Γ : Context} {a : Term Γ} → (Γ ⊢ a ≈ (a [ id-substitution ]s))
  id-action {a = tm-var a} = eq-refl
  id-action {a = tm-oper f x} = eq-congr (λ i → id-action {Σ} {a = x i})

  -- an equality is preserved by the action of the identity
  eq-id-action : ∀ {Σ : Signature} {Γ : Context} {u v : Term Γ} → (Γ ⊢ (u [ id-substitution ]s) ≈ (v [ id-substitution ]s)) → (Γ ⊢ u ≈ v)
  eq-id-action {u = u} {v = v} p = eq-tran (id-action {Σ} {a = u}) (eq-tran p (eq-symm (id-action {Σ} {a = v})))

  -- equality of substitutions
  _≈s_ : ∀ {Γ Δ : Context} → substitution Σ Γ Δ → substitution Σ Γ Δ → Set (lsuc ℓ)
  _≈s_ {Γ = Γ} σ ρ = ∀ x → Γ ⊢ σ x ≈ ρ x

  -- reflexivity of the equality of substitutions
  refl-subst : ∀ {Γ Δ : Context} {f : substitution Σ Γ Δ} → f ≈s f
  refl-subst = λ x → eq-refl

  -- symmetry of the equality of substitutions
  symm-subst : ∀ {Γ Δ : Context} {f g : substitution Σ Γ Δ} → f ≈s g → g ≈s f
  symm-subst {Γ} {Δ} {f} {g} p = λ x → eq-symm (p x)

  -- transitivity of the equality of substitutions
  trans-subst : ∀ {Γ Δ : Context} {f g h : substitution Σ Γ Δ} → f ≈s g → g ≈s h → f ≈s h
  trans-subst {Γ} {Δ} {f} {g} {h} p q = λ x → eq-tran (p x) (q x)

  -- neutrality of tm-var
  tm-var-id : ∀ {Γ : Context} {x : Term Γ} → Γ ⊢ x [ id-substitution ]s ≈ x
  tm-var-id {x = tm-var x} = eq-refl
  tm-var-id {x = tm-oper f x} = eq-congr (λ i → tm-var-id)

  -- any two substitutions into the empty context are equal
  empty-context-unique : ∀ {Γ : Context} {σ ρ : substitution Σ Γ empty-context} → σ ≈s ρ
  empty-context-unique ()

  -- composition of substitutions is functorial
  subst-∘s : ∀ {Γ Δ Θ} {ρ : substitution Σ Δ Γ} {σ : substitution Σ Θ Δ} (t : Term Γ) → Θ ⊢ (t [ ρ ]s) [ σ ]s ≈ t [ ρ ∘s σ ]s
  subst-∘s (tm-var x) = eq-refl
  subst-∘s (tm-oper f ts) = eq-congr (λ i → subst-∘s (ts i))

  -- substitution preserves equality
  eq-subst : ∀ {Γ Δ : Context} (σ : substitution Σ Γ Δ) {u v : Term Δ} → Δ ⊢ u ≈ v → Γ ⊢ u [ σ ]s ≈ v [ σ ]s
  eq-subst σ eq-refl = eq-refl
  eq-subst σ (eq-symm ξ) = eq-symm (eq-subst σ ξ)
  eq-subst σ (eq-tran ζ ξ) = eq-tran (eq-subst σ ζ) (eq-subst σ ξ)
  eq-subst σ (eq-congr ξ) = eq-congr (λ i → eq-subst σ (ξ i))
  eq-subst σ (eq-axiom ε ρ) = eq-tran (subst-∘s (eq-lhs ε)) (eq-tran (eq-axiom ε (ρ ∘s σ)) (eq-symm (subst-∘s (eq-rhs ε))))

 -- equivalent substitutions act the same on terms
  equiv-subst : ∀ {Γ Δ : Context} (f g : substitution Σ Γ Δ)  → f ≈s g → ( ∀ x → Γ ⊢ x [ f ]s ≈ x [ g ]s)
  equiv-subst f g p (tm-var x) = p x
  equiv-subst f g p (tm-oper f₁ x) = eq-congr (λ i → equiv-subst f g p (x i))

 -- equivalent substitution preserve equality
  equiv-eq-subst : ∀ {Γ Δ : Context} (f g : substitution Σ Γ Δ) {u v : Term Δ} (p : f ≈s g) → Δ ⊢ u ≈ v → Γ ⊢ u [ f ]s ≈ v [ g ]s
  equiv-eq-subst f g {u} {.u} p eq-refl = equiv-subst f g p u
  equiv-eq-subst f g {u} {v} p (eq-symm q) = eq-symm  (equiv-eq-subst g f {v} {u} (symm-subst p) q)
  equiv-eq-subst f g {u} {v} p (eq-tran {t = t} q q₁ ) =  eq-tran (eq-subst f q) (equiv-eq-subst f g {t} {v} (p) q₁)
  equiv-eq-subst {Γ} {Δ} f g {.(tm-oper _ _)} {.(tm-oper  _ _)} p (eq-congr x) = eq-congr λ i → equiv-eq-subst f g p (x i)
  equiv-eq-subst f g {.(eq-lhs ε [ σ ]s)} {.(eq-rhs ε [ σ ]s)} p (eq-axiom ε σ) = eq-tran (eq-subst f (eq-axiom ε σ)) (equiv-subst f g p (eq-rhs ε [ σ ]s))
