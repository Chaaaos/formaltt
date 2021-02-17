module ManySortedAlgebra where

  -- a many sorted signature
  record Signature : Set₁ where
    field
      sort : Set -- sorts
      op : Set -- operations
      arg : op → Set
      op-sort : op → sort -- the sort of the operation
      arg-sort : ∀ {f} → arg f → sort -- the sorts of arguments

  open Signature

  -- we allow general contexts in which there are arbitrarily many variables,
  -- which makes things easier
  record Context (Σ : Signature) : Set₁ where
    field
      var : Set
      var-sort : var → sort Σ

  open Context

  -- terms over a signature in a context of a given sort
  data Term {Σ : Signature} (Γ : Context Σ) : sort Σ → Set where
    tm-var : ∀ (x : var Γ) → Term Γ (var-sort Γ x)
    tm-op : ∀ (f : op Σ) → (∀ (i : arg Σ f) → Term Γ (arg-sort Σ i)) → Term Γ (op-sort Σ f)

  substitution : ∀ {Σ : Signature} (Γ Δ : Context Σ) → Set
  substitution Γ Δ = ∀ (x : var Γ) → Term Δ (var-sort Γ x)

  -- the action of a substitution on a term
  _·_ : ∀ {Σ : Signature} {Γ Δ : Context Σ} → substitution Γ Δ → ∀ {A} → Term Γ A → Term Δ A
  σ · (tm-var x) = σ x
  σ · (tm-op f x) = tm-op f (λ i → σ · x i)

  infixr 6 _·_

  -- composition of substitutions
  _○_ : ∀ {Σ : Signature} {Γ Δ Θ : Context Σ} → substitution Δ Θ → substitution Γ Δ → substitution Γ Θ
  (σ ○ τ) x = σ · τ x

  infixl 7 _○_

  -- an equational theory is a family of equations over a given sort
  record EquationalTheory (Σ : Signature) : Set₁ where
    field
      eq : Set
      eq-ctx : ∀ (ε : eq) → Context Σ
      eq-sort : ∀ (ε : eq) → sort Σ
      eq-lhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε)
      eq-rhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε)

  open EquationalTheory

  infix 4 _≡_

  -- the remaining judgement form is equality
  data _≡_ {Σ : Signature} {T : EquationalTheory Σ} : {Γ : Context Σ} → {S : sort Σ} → Term Γ S → Term Γ S → Set₁ where
    -- general rules
    eq-refl : ∀ {Γ} {S : sort Σ} {t : Term Γ S} → t ≡ t
    eq-symm : ∀ {Γ} {S : sort Σ} {s t : Term {Σ} Γ S} → _≡_ {T = T} s t → t ≡ s
    eq-tran : ∀ {Γ} {S : sort Σ} {s t u : Term Γ S} → _≡_ {T = T} s t → _≡_ {T = T} t u → s ≡ u
    -- congruence rule
    eq-congr : ∀ {Γ} {f : op Σ} (x y : ∀ (i : arg Σ f) → Term Γ (arg-sort Σ i)) →
               (∀ i → _≡_ {_} {T} (x i) (y i)) → tm-op f x ≡ tm-op f y
    -- equational axiom
    eq-axiom : ∀ (ε : eq T) {Δ} (σ : substitution (eq-ctx T ε) Δ) →
               σ · eq-lhs T ε ≡ σ · eq-rhs T ε

  -- composition is functorial
  subst-○ : ∀ {Σ : Signature} {T : EquationalTheory Σ} {Γ Δ Θ : Context Σ}
              (σ : substitution Δ Θ) (τ : substitution Γ Δ) →
              ∀ {A} (t : Term Γ A) → _≡_ {T = T} (σ · τ · t)  (σ ○ τ · t)
  subst-○ σ τ (tm-var x) = eq-refl
  subst-○ σ τ (tm-op f x) = eq-congr (λ i → σ · τ · x i) (λ i → σ ○ τ · x i) λ i → subst-○ σ τ (x i)

  -- substitution preserves equality
  eq-subst : ∀ {Σ : Signature} {T : EquationalTheory Σ} {Γ Δ : Context Σ} {S : sort Σ} (σ : substitution Γ Δ)
               {s t : Term Γ S} → _≡_ {T = T} s t → _≡_ {T = T} (σ · s) (σ · t)
  eq-subst σ eq-refl = eq-refl
  eq-subst σ (eq-symm ξ) = eq-symm (eq-subst σ ξ)
  eq-subst σ (eq-tran ζ ξ) = eq-tran (eq-subst σ ζ) (eq-subst σ ξ)
  eq-subst σ (eq-congr x y ξ) = eq-congr (λ i → σ · x i) (λ i → σ · y i) λ i → eq-subst σ (ξ i)
  eq-subst {T = T} σ (eq-axiom ε τ) =
    eq-tran (subst-○ σ τ (eq-lhs T ε))
            (eq-tran (eq-axiom ε (σ ○ τ)) (eq-symm (subst-○ σ τ (eq-rhs T ε))))
