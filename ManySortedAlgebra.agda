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

  -- an equational theory is a family of equations over a given sort
  record EquationalTheory (Σ : Signature) : Set₁ where
    field
      eq : Set
      eq-ctx : ∀ (ε : eq) → Context Σ
      eq-sort : ∀ (ε : eq) → sort Σ
      eq-lhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε)
      eq-rhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε)

  open EquationalTheory

  -- the remaining judgement form is equality
  data _≡_ {Σ : Signature} {T : EquationalTheory Σ} : {Γ : Context Σ} → {S : sort Σ} → Term Γ S → Term Γ S → Set where
    -- general rules
    eq-refl : ∀ {Γ} {S : sort Σ} {t : Term Γ S} → t ≡ t
    eq-symm : ∀ {Γ} {S : sort Σ} {s t : Term Γ S} → _≡_ {_} {T} s t → t ≡ s
    eq-tran : ∀ {Γ} {S : sort Σ} {s t u : Term Γ S} → _≡_ {_} {T} s t → _≡_ {_} {T} t u → s ≡ u
    -- congruence rule
    eq-congr : ∀ {Γ} {f : op Σ} (x y : ∀ (i : arg Σ f) → Term Γ (arg-sort Σ i)) →
               (∀ {i} → _≡_ {_} {T} (x i) (y i)) → tm-op f x ≡ tm-op f y
    -- equational axiom
    eq-axiom : ∀ {ε : eq T} → eq-lhs T ε ≡ eq-rhs T ε
