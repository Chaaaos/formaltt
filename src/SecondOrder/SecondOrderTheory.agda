open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

import SecondOrder.Context as Context

module SecondOrder.SecondOrderTheory where

  -- We work over a given notion of arity
  record Arity : Set₁ where
    field
      arity : Set -- the set of permissible arities, e.g., ℕ
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

    mv-arg : ∀ (Θ : MetaContext) → mv Θ → Set
    mv-arg Θ M = var (mv-arity Θ M)

    mv-arg-sort : ∀ (Θ : MetaContext) (M : mv Θ) → mv-arg Θ M → sort
    mv-arg-sort Θ M i = sort-of (mv-arity Θ M) i

    -- terms in a context of a given sort
    data Term (Θ : MetaContext) : ∀ (Γ : Context)  (A : sort) → Set (lsuc (ℓa ⊔ ℓo ⊔ ℓs)) where
      tm-var : ∀ {Γ} (x : var Γ) → Term Θ Γ (sort-of Γ x)
      tm-meta : ∀ {Γ} (M : mv Θ) (ts : ∀ (i : mv-arg Θ M) → Term Θ Γ (mv-arg-sort Θ M i)) → Term Θ Γ (mv-sort Θ M)
      tm-oper : ∀ {Γ} (f : oper)
                  (es : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i)) →
                  Term Θ Γ (oper-sort f)

    -- Variable renamings and substitition
    module _ {Θ : MetaContext} where

      -- a variable renaming is a map from variable to variables that preserves types
      record Renaming (Γ Δ : Context) : Set ℓs where
        field
          var-rename : var Γ → var Δ
          var-resp : ∀ x → sort-of Δ (var-rename x) ≡ sort-of Γ x

      open Renaming

      -- extend a renaming by a context
      extend : ∀ {Γ Δ} → Renaming Γ Δ → ∀ Ξ → Renaming (Γ ,, Ξ) (Δ ,, Ξ)
      extend {Γ} {Δ} ρ Ξ = σ where
        σ : Renaming (Γ ,, Ξ) (Δ ,, Ξ)
        var-rename σ (var-inl x) = var-inl (var-rename ρ x)
        var-rename σ (var-inr y) = var-inr y
        var-resp σ (var-inl x) = var-resp ρ x
        var-resp σ (var-inr y) = refl

      -- the action of a renaming on a term
      tm-rename : ∀ {Γ Δ A} → Renaming Γ Δ → Term Θ Γ A → Term Θ Δ A
      tm-rename ρ (tm-var x) = {!!}
      tm-rename ρ (tm-meta M ts) = tm-meta M λ i → tm-rename ρ (ts i)
      tm-rename ρ (tm-oper f es) = tm-oper f (λ i → tm-rename (extend ρ (arg-bind f i)) (es i))

      weakening : ∀ {Γ Δ} → Renaming Γ (Γ ,, Δ)
      var-rename weakening x = var-inl x
      var-resp weakening x = refl

      ctx-swap : ∀ {Γ Δ Ξ A} → Term Θ ((Γ ,, Δ) ,, Ξ) A → Term Θ ((Γ ,, Ξ) ,, Δ) A
      ctx-assoc : ∀ {Γ Δ Ξ A} → Term Θ ((Γ ,, Δ) ,, Ξ) A → Term Θ (Γ ,, (Δ ,, Ξ)) A

      ctx-swap (tm-var (var-inl (var-inl x))) = tm-var (var-inl (var-inl x))
      ctx-swap (tm-var (var-inl (var-inr y))) = tm-var (var-inr y)
      ctx-swap (tm-var (var-inr z)) = tm-var (var-inl (var-inr z))
      ctx-swap (tm-meta M ts) = tm-meta M (λ i → ctx-swap (ts i))
      ctx-swap (tm-oper f es) = tm-oper f (λ i → {!ctx-assoc!} )

      ctx-assoc (tm-var x) = {!!}
      ctx-assoc (tm-meta M ts) = {!!}
      ctx-assoc (tm-oper f es) = tm-oper f (λ i → {!!})

      wkn : ∀ {Γ Δ A} → Term Θ Γ A → Term Θ (Γ ,, Δ) A
      wkn (tm-var x) = tm-var (var-inl x)
      wkn (tm-meta M ts) = tm-meta M (λ i → wkn (ts i))
      wkn (tm-oper f es) = tm-oper f (λ i → ctx-swap (wkn (es i)))

      -- substitition
      _⇒s_ : ∀ (Γ Δ : Context) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
      Γ ⇒s Δ = ∀ (x : var Δ) → Term Θ Γ (sort-of Δ x)

      infix 4 _⇒s_

      -- shifting a substitution
      shift : ∀ {Γ Δ Ξ} → Γ ⇒s Δ → Γ ,, Ξ ⇒s Δ ,, Ξ
      shift σ (var-inl x) = wkn (σ x)
      shift σ (var-inr x) = tm-var (var-inr x)

      -- the action of a substitution on a term (contravariant)
      _[_]s : ∀ {Γ Δ : Context} {A : sort} → Term Θ Δ A → Γ ⇒s Δ → Term Θ Γ A
      (tm-var x) [ σ ]s = σ x
      (tm-meta M ts) [ σ ]s = tm-meta M (λ i → (ts i) [ σ ]s)
      (tm-oper f es) [ σ ]s = tm-oper f (λ i → es i [ shift σ ]s)

      infixr 6 _[_]s

      -- identity substitution
      id-s : ∀ {Γ : Context} → Γ ⇒s Γ
      id-s = tm-var

      -- -- composition of substitutions
      -- _∘s_ : ∀ {Γ Δ Θ : Context} → Δ ⇒s Θ → Γ ⇒s Δ → Γ ⇒s Θ
      -- (σ ∘s ρ) x = σ x [ ρ ]s

      -- infixl 7 _∘s_
