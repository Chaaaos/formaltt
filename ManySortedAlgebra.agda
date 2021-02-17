module ManySortedAlgebra where

  -- a many sorted signature
  record Signature : Set₁ where
    field
      sort : Set
      op : Set
      op-sort : op → sort
      arg : op → Set
      arg-sort : ∀ {o} → arg o → sort

  open Signature

  record Context (Σ : Signature) : Set₁ where
    field
      var : Set
      var-sort : var → sort Σ

  open Context

  -- terms over a signature
  data Term {Σ : Signature} (Γ : Context Σ) : sort Σ → Set where
    tm-var : ∀ (x : var Γ) → Term Γ (var-sort Γ x)
    tm-op : ∀ (f : op Σ) → (∀ (i : arg Σ f) → Term Γ (arg-sort Σ i)) → Term Γ (op-sort Σ f)

  record EqSignature (Σ : Signature) : Set₁ where
    field
      eq : Set
      eq-ctx : ∀ (ε : eq) → Context Σ
      eq-sort : ∀ (ε : eq) → sort Σ
      eq-lhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε)
      eq-rhs : ∀ (ε : eq) → Term (eq-ctx ε) (eq-sort ε)

  open EqSignature

  data _≡_ {Σ : Signature} {E : EqSignature Σ} : {Γ : Context Σ} → {S : sort Σ} → Term Γ S → Term Γ S → Set where
    -- general rules
    eq-refl : ∀ {Γ} {S : sort Σ} {t : Term Γ S} → t ≡ t
    eq-symm : ∀ {Γ} {S : sort Σ} {s t : Term Γ S} → _≡_ {_} {E} s t → t ≡ s
    eq-tran : ∀ {Γ} {S : sort Σ} {s t u : Term Γ S} → _≡_ {_} {E} s t → _≡_ {_} {E} t u → s ≡ u
    -- congruence rules
    eq-congr : ∀ {Γ} {f : op Σ} (x y : ∀ (i : arg Σ f) → Term Γ (arg-sort Σ i)) →
               (∀ {i} → _≡_ {_} {E} (x i) (y i)) → tm-op f x ≡ tm-op f y
    -- equational axiom
    eq-axiom : ∀ {ε : eq E} → eq-lhs E ε ≡ eq-rhs E ε
