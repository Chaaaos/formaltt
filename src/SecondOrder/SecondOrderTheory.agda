open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

import SecondOrder.Context as Context

module SecondOrder.SecondOrderTheory where

  -- We work over a given notion of arity
  record Arity : Set₁ where
    field
      arity : Set -- the set of permissible arities, e.g., ℕ for finitary arities
      arg : arity → Set -- every arity gives a set of argument (position), e.g. Fin

  -- a second-order algebraic signature
  record Signature {ℓs ℓo ℓa} (𝔸 : Arity) : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
    open Arity 𝔸

    field
      sort : Set ℓs -- sorts
      oper : Set ℓo -- operations

    open Context sort public

    field
      oper-arity : oper → arity -- the arity of an operation
      oper-sort : oper → sort -- the operation sort
      arg-sort : ∀ (f : oper) → arg (oper-arity f) → sort -- the sorts of arguments
      arg-bind : ∀ (f : oper) → arg (oper-arity f) → Context -- the argument bindings

    -- the arguments of an operation
    oper-arg : oper → Set
    oper-arg f = arg (oper-arity f)

    -- a metavariable context
    record MetaContext : Set (lsuc ℓs) where
      field
        mv : Set ℓs -- the metavariables
        mv-arity : mv → Context -- the arity of a metavariable
        mv-sort : mv → sort -- the sort of a metavariable

    open MetaContext public

    infix 4 _∈ᴹ_

    mv-arg : ∀ (Θ : MetaContext) → mv Θ → sort → Set ℓs
    mv-arg Θ M A = A ∈ (mv-arity Θ M)

    -- terms in a context of a given sort
    data Term (Θ : MetaContext) : ∀ (Γ : Context) (A : sort) → Set (lsuc (ℓa ⊔ ℓo ⊔ ℓs)) where
      tm-var : ∀ {Γ} {A} (x : A ∈ Γ) → Term Θ Γ A
      tm-meta : ∀ {Γ} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B) → Term Θ Γ (mv-sort Θ M)
      tm-oper : ∀ {Γ} (f : oper)
                  (es : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i)) →
                  Term Θ Γ (oper-sort f)

    -- Substititions
    module _ {Θ : MetaContext} where

      infix 4 _⇒r_

      _⇒r_ : ∀ (Γ Δ : Context) → Set ℓs
      Γ ⇒r Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

      extend-r : ∀ {Γ Δ} → Γ ⇒r Δ → ∀ {Ξ} → Γ ,, Ξ ⇒r Δ ,, Ξ
      extend-r ρ (var-inl x) = var-inl (ρ x)
      extend-r ρ (var-inr x) = var-inr x

      tm-rename : ∀ {Γ Δ A} → Γ ⇒r Δ → Term Θ Γ A → Term Θ Δ A
      tm-rename ρ (tm-var x) = tm-var (ρ x)
      tm-rename ρ (tm-meta M ts) = tm-meta M (λ i → tm-rename ρ (ts i))
      tm-rename ρ (tm-oper f es) = tm-oper f (λ i → tm-rename (extend-r ρ) (es i))

      weaken : ∀ {Γ Δ A} → Term Θ Γ A → Term Θ (Γ ,, Δ) A
      weaken = tm-rename var-inl

      -- substitition
      _⇒s_ : ∀ (Γ Δ : Context) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
      Γ ⇒s Δ = ∀ {A} (x : A ∈ Δ) → Term Θ Γ A

      infix 4 _⇒s_

      -- extending a substitution
      extend-s : ∀ {Γ Δ Ξ} → Γ ⇒s Δ → Γ ,, Ξ ⇒s Δ ,, Ξ
      extend-s {Ξ = Ξ} σ (var-inl x) = weaken (σ x)
      extend-s σ (var-inr x) = tm-var (var-inr x)

      -- the action of a substitution on a term (contravariant)
      _[_]s : ∀ {Γ Δ : Context} {A : sort} → Term Θ Δ A → Γ ⇒s Δ → Term Θ Γ A
      (tm-var x) [ σ ]s = σ x
      (tm-meta M ts) [ σ ]s = tm-meta M (λ i → (ts i) [ σ ]s)
      (tm-oper f es) [ σ ]s = tm-oper f (λ i → es i [ extend-s σ ]s)

      infixr 6 _[_]s

      -- identity substitution
      id-s : ∀ {Γ : Context} → Γ ⇒s Γ
      id-s = tm-var

      -- composition of substitutions
      _∘s_ : ∀ {Γ Δ Θ : Context} → Δ ⇒s Θ → Γ ⇒s Δ → Γ ⇒s Θ
      (σ ∘s ρ) x = σ x [ ρ ]s

      infixl 7 _∘s_

      -- TODO:

      -- define what an equation is

      -- define what a theory is
