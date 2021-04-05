open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

import MultiSorted.Context as Context

module SecondOrder.SecondOrderTheory where

  -- a second-order algebraic signature
  record Signature {ℓs ℓo ℓa} : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
    field
      sort : Set ℓs -- sorts
      oper : Set ℓo -- operations
      arity : Set ℓa
      slot : arity → Set ℓa

    open Context sort public

    field
      oper-arity : oper → arity -- the arity of an operation (with the sorts of the arguments)
      oper-sort : oper → sort -- the sort of an operation
      arg-sort : ∀ (f : oper) → slot (oper-arity f) → sort -- the sort of an argument
      arg-bind : ∀ (f : oper) → slot (oper-arity f) → Context

    oper-arg : oper → Set ℓa
    oper-arg f = slot (oper-arity f)

    record Meta : Set (lsuc ℓs) where
      field
        mv : Set ℓs
        mv-arity : mv → Context
        mv-sort : mv → sort

    open Meta public

    mv-arg : ∀ (Θ : Meta) → mv Θ → Set
    mv-arg Θ M = var (mv-arity Θ M)

    mv-arg-sort : ∀ (Θ : Meta) (M : mv Θ) → mv-arg Θ M → sort
    mv-arg-sort Θ M i = sort-of (mv-arity Θ M) i

    -- terms in a context of a given sort
    data Term (Θ : Meta) (Γ : Context) : ∀ (A : sort) → Set (lsuc (ℓa ⊔ ℓo ⊔ ℓs)) where
      tm-var : ∀ (x : var Γ) → Term Θ Γ (sort-of Γ x)
      tm-meta : ∀ (M : mv Θ) → (∀ (i : mv-arg Θ M) → Term Θ Γ (mv-arg-sort Θ M i)) → Term Θ Γ (mv-sort Θ M)
      tm-oper : ∀ (f : oper) →
                  (∀ (i : oper-arg f) → Term Θ (ctx-concat Γ (arg-bind f i)) (arg-sort f i)) →
                  Term Θ Γ (oper-sort f)

    -- Substitutions (definitions - some useful properties are in another file)
    module _ {Θ : Meta} where

      _⇒s_ : ∀ (Γ Δ : Context) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
      Γ ⇒s Δ = ∀ (x : var Δ) → Term Θ Γ (sort-of Δ x)

      infix 4 _⇒s_

      -- identity substitution
      id-s : ∀ {Γ : Context} → Γ ⇒s Γ
      id-s = tm-var

      -- variable renaming
      record Renaming (Γ Δ : Context) : Set ℓs where
        field
          var-rename : var Γ → var Δ
          var-resp : ∀ x → sort-of Δ (var-rename x) ≡ sort-of Γ x

      open Renaming

      var-coerce : ∀ {Γ Δ} → Renaming Γ Δ → ∀ (x : var Γ) → Term Θ Δ (sort-of Γ x)
      var-coerce {Γ} {Δ} ρ x = subst (Term Θ Δ) (var-resp ρ x) (tm-var (var-rename ρ x))

      extend : ∀ {Γ Δ} → Renaming Γ Δ → ∀ Ξ → Renaming (ctx-concat Γ Ξ) (ctx-concat Δ Ξ)
      extend {Γ} {Δ} ρ Ξ = σ where
        σ : Renaming (ctx-concat Γ Ξ) (ctx-concat Δ Ξ)
        var-rename σ (var-inl x) = var-inl (var-rename ρ x)
        var-rename σ (var-inr y) = var-inr y
        var-resp σ (var-inl x) = var-resp ρ x
        var-resp σ (var-inr y) = refl

      tm-rename : ∀ {Γ Δ A} → Renaming Γ Δ → Term Θ Γ A → Term Θ Δ A
      tm-rename ρ (tm-var x) = var-coerce ρ x
      tm-rename ρ (tm-meta M ts) = tm-meta M λ i → tm-rename ρ (ts i)
      tm-rename ρ (tm-oper f es) = tm-oper f (λ i → tm-rename (extend ρ (arg-bind f i)) (es i))

      weakening : ∀ {Γ Δ} → Renaming Γ (ctx-concat Γ Δ)
      var-rename weakening x = var-inl x
      var-resp weakening x = refl

      -- shifting a substitution
      shift : ∀ {Γ Δ Ξ} → Γ ⇒s Δ → (ctx-concat Γ Ξ) ⇒s (ctx-concat Δ Ξ)
      shift σ (var-inl x) = tm-rename weakening (σ x)
      shift σ (var-inr y) = tm-var (var-inr y)

      -- the action of a substitution on a term (contravariant)
      _[_]s : ∀ {Γ Δ : Context} {A : sort} → Term Θ Δ A → Γ ⇒s Δ → Term Θ Γ A
      (tm-var x) [ σ ]s = σ x
      (tm-meta M ts) [ σ ]s = tm-meta M (λ i → (ts i) [ σ ]s)
      (tm-oper f es) [ σ ]s = tm-oper f (λ i → es i [ shift σ ]s)

      infixr 6 _[_]s

      -- -- composition of substitutions
      -- _∘s_ : ∀ {Γ Δ Θ : Context} → Δ ⇒s Θ → Γ ⇒s Δ → Γ ⇒s Θ
      -- (σ ∘s ρ) x = σ x [ ρ ]s

      -- infixl 7 _∘s_
