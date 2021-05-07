-- {-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc; _⊔_; Level)
open import Relation.Unary hiding (_∈_)
open import Data.Empty.Polymorphic
open import Data.List
open import Function.Base
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import SecondOrder.Arity

import SecondOrder.SecondOrderSignature as SecondOrderSignature

module SecondOrder.Substitution {ℓs ℓo ℓa : Level} {𝔸 : Arity} {Σ : SecondOrderSignature.Signature {ℓs} {ℓo} {ℓa} 𝔸}where

  open SecondOrderSignature {ℓs} {ℓo} {ℓa}
  open Signature 𝔸 Σ



    -- ** Renamings **

  -- a renaming is a morphism between scopes
  -- renaming
  _⊕_⇒r_ : ∀ (Θ : MetaContext) (Γ Δ : Context) → Set ℓs
  Θ ⊕ Γ ⇒r Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

  infix 4 _⊕_⇒r_


  module _ {Θ : MetaContext}  where

      -- extending a renaming
      extend-r : ∀ {Γ Δ} → Θ ⊕ Γ ⇒r Δ → ∀ {Ξ} → Θ ⊕ Γ ,, Ξ ⇒r Δ ,, Ξ
      extend-r ρ (var-inl x) = var-inl (ρ x)
      extend-r ρ (var-inr y) = var-inr y

      -- the identity renaming
      id-r : ∀ {Γ : Context} → Θ ⊕ Γ ⇒r Γ
      id-r x = x

      -- composition of renamings
      _∘r_ : ∀ {Γ Δ Ξ : Context} → Θ ⊕ Δ ⇒r Ξ → Θ ⊕ Γ ⇒r Δ → Θ ⊕ Γ ⇒r Ξ
      (σ ∘r ρ) x = σ (ρ x)

      infix 7 _∘r_

      -- action of a renaming on terms
      [_]r_ : ∀ {Γ Δ A} → Θ ⊕ Γ ⇒r Δ → Term Θ Γ A → Term Θ Δ A
      [ ρ ]r (tm-var x) = tm-var (ρ x)
      [ ρ ]r (tm-meta M ts) = tm-meta M (λ i → [ ρ ]r (ts i))
      [ ρ ]r (tm-oper f es) = tm-oper f (λ i → [ (extend-r ρ) ]r (es i))

      infix 6 [_]r_

      -- the reassociation renaming
      rename-assoc-r : ∀ {Γ Δ Ξ} → Θ ⊕ (Γ ,, Δ) ,, Ξ ⇒r Γ ,, (Δ ,, Ξ)
      rename-assoc-r (var-inl (var-inl x)) = var-inl x
      rename-assoc-r (var-inl (var-inr y)) = var-inr (var-inl y)
      rename-assoc-r (var-inr z) = var-inr (var-inr z)

      rename-assoc-l : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ,, (Δ ,, Ξ) ⇒r (Γ ,, Δ) ,, Ξ
      rename-assoc-l (var-inl x) = var-inl (var-inl x)
      rename-assoc-l (var-inr (var-inl y)) = var-inl (var-inr y)
      rename-assoc-l (var-inr (var-inr z)) = var-inr z

      -- apply the reassociation renaming on terms
      term-reassoc : ∀ {Δ Γ Ξ A}
        → Term Θ (Δ ,, (Γ ,, Ξ)) A
        → Term Θ ((Δ ,, Γ) ,, Ξ) A
      term-reassoc = [ rename-assoc-l ]r_

      -- the empty context is the unit
      rename-ctx-empty-r : ∀ {Γ} → Θ ⊕ Γ ,, ctx-empty ⇒r Γ
      rename-ctx-empty-r (var-inl x) = x

      rename-ctx-empty-inv : ∀ {Γ} → Θ ⊕ Γ ⇒r Γ ,, ctx-empty
      rename-ctx-empty-inv x = var-inl x

      -- weakening
      weakenˡ : ∀ {Γ Δ A} → Term Θ Γ A → Term Θ (Γ ,, Δ) A
      weakenˡ = [ var-inl ]r_

      weakenʳ : ∀ {Γ Δ A} → Term Θ Δ A → Term Θ (Γ ,, Δ) A
      weakenʳ = [ var-inr ]r_

      -- this is probably useless to have a name for
      -- but it allows us to use the extended renaming as a fuction from terms to terms
      app-extend-r : ∀ {Γ Δ Ξ A} → Θ ⊕ Γ ⇒r Δ → Term Θ (Γ ,, Ξ) A → Term Θ (Δ ,, Ξ) A
      app-extend-r ρ t = [ extend-r ρ ]r t



    -- ** Substitutions **

  -- substitition
  _⊕_⇒s_ : ∀ (Θ : MetaContext) (Γ Δ : Context) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
  Θ ⊕ Γ ⇒s Δ = ∀ {A} (x : A ∈ Δ) → Term Θ Γ A

  infix 4 _⊕_⇒s_

  module _ {Θ : MetaContext}  where

      -- extending a substitution
      extend-sˡ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒s Δ → Θ ⊕ (Γ ,, Ξ) ⇒s (Δ ,, Ξ)
      extend-sˡ {Ξ = Ξ} σ (var-inl x) = weakenˡ (σ x)
      extend-sˡ σ (var-inr x) = tm-var (var-inr x)

      extend-sʳ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒s Δ → Θ ⊕ Ξ ,, Γ ⇒s Ξ ,, Δ
      extend-sʳ {Ξ = Ξ} σ (var-inl x) = tm-var (var-inl x)
      extend-sʳ σ (var-inr x) = weakenʳ (σ x)

      -- the action of a substitution on a term (contravariant)
      _[_]s : ∀ {Γ Δ : Context} {A : sort} → Term Θ Δ A → Θ ⊕ Γ ⇒s Δ → Term Θ Γ A
      (tm-var x) [ σ ]s = σ x
      (tm-meta M ts) [ σ ]s = tm-meta M (λ i → (ts i) [ σ ]s)
      (tm-oper f es) [ σ ]s = tm-oper f (λ i → es i [ extend-sˡ σ ]s)

      infixr 6 _[_]s

      -- identity substitution
      id-s : ∀ {Γ : Context} → Θ ⊕ Γ ⇒s Γ
      id-s = tm-var

      -- application of extension
      -- this is probably useless to have a name for, but it does give a way to make a
      -- function to go from Terms to Terms
      app-extend-sˡ : ∀ {Γ Δ Ξ A} → Θ ⊕ Γ ⇒s Δ → Term Θ (Δ ,, Ξ) A → Term Θ (Γ ,, Ξ) A
      app-extend-sˡ σ t = t [ extend-sˡ σ ]s

      -- composition of substitutions
      _∘s_ : ∀ {Γ Δ Ξ : Context} → Θ ⊕ Δ ⇒s Ξ → Θ ⊕ Γ ⇒s Δ → Θ ⊕ Γ ⇒s Ξ
      (σ ∘s ρ) x = σ x [ ρ ]s

      infixl 7 _∘s_

      -- action of a renaming on a substitution
      _r∘s_ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒r Δ → Θ ⊕ Ξ ⇒s Δ → Θ ⊕ Ξ ⇒s Γ
      (ρ r∘s σ) x = σ (ρ x)

      -- action of a substitution on a renaming
      _s∘r_ : ∀ {Γ Δ Ξ} → Θ ⊕ Δ ⇒s Γ → Θ ⊕ Δ ⇒r Ξ → Θ ⊕ Ξ ⇒s Γ
      (σ s∘r ρ) x = [ ρ ]r (σ x)



      -- ** Metavariable instantiations **

  -- metavariable instantiation
  _⇒M_⊕_  : MetaContext → MetaContext → Context → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
  ψ ⇒M Θ ⊕ Γ = ∀ (M : mv Θ) → Term ψ (Γ ,, mv-arity Θ M) (mv-sort Θ M)

  -- action of a metavariable instantiation on terms
  _[_]M : ∀ {Γ : Context} {A : sort} {Θ Ψ : MetaContext} {Δ} → Term Θ Γ A → ∀ (ι : Ψ ⇒M Θ ⊕ Δ) → Term Ψ (Δ ,, Γ) A

  []M-mv : ∀ {Γ : Context} {Θ Ψ : MetaContext} {Δ} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B) (ι : Ψ ⇒M Θ ⊕ Δ) → Ψ ⊕ Δ ,, Γ ⇒s Δ ,, mv-arity Θ M

  []M-mv M ts ι (var-inl x) = tm-var (var-inl x)
  []M-mv M ts ι (var-inr x) =  (ts x) [ ι ]M

  (tm-var x) [ ι ]M = tm-var (var-inr x)
  _[_]M {Γ = Γ} {Θ = Θ} {Δ = Δ} (tm-meta M ts) ι = (ι M) [ []M-mv M ts ι ]s
  _[_]M {Ψ = Ψ} (tm-oper f es) ι = tm-oper f (λ i → [ (rename-assoc-l {Θ = Ψ}) ]r (es i [ ι ]M) )

  infixr 6 _[_]M

  -- the identity metavariable instantiation
  id-M : ∀ {Θ} → Θ ⇒M Θ ⊕ ctx-empty
  id-M t = tm-meta t (λ i → weakenʳ (tm-var i))

  id-M-inv : ∀ {Θ Γ} → Θ ⊕ (ctx-empty ,, Γ) ⇒r Γ
  id-M-inv (var-inr x) = x

  -- composition of metavariable instantiations
  _∘M_ : ∀ {Θ ψ Ω Γ Δ} → Ω ⇒M ψ ⊕ Δ → ψ ⇒M Θ ⊕ Γ → (Ω ⇒M Θ ⊕ (Δ ,, Γ))
  _∘M_ {Θ = Θ} {ψ = ψ} {Γ = Γ} {Δ = Δ} μ ι = λ M → term-reassoc (ι M [ μ ]M)



    -- ** Interactions **

  -- action of a metavariable instantiation on a substitution
  _M∘s_ : ∀ {Θ ψ Γ Δ Ξ} → ψ ⇒M Θ ⊕ Ξ → Θ ⊕ Δ ⇒s Γ → ψ ⊕ (Ξ ,, Δ) ⇒s (Ξ ,, Γ)
  (ι M∘s σ) (var-inl x) = tm-var (var-inl x)
  (ι M∘s σ) (var-inr x) = σ x [ ι ]M

  -- action of a substitution on a metavariable instantiation
  _s∘M_ : ∀ {Θ ψ Γ Δ} → ψ ⊕ Δ ⇒s Γ → ψ ⇒M Θ ⊕ Γ → ψ ⇒M Θ ⊕ Δ
  _s∘M_ σ ι M = ι M [ extend-sˡ σ ]s

  -- action of a renaming on a metavariable instantiation
  _r∘M_ : ∀ {Θ ψ Δ Ξ} → ψ ⇒M Θ ⊕ Ξ → Θ ⊕ Ξ ⇒r Δ → ψ ⇒M Θ ⊕ Δ
  _r∘M_ {Θ = Θ} ι ρ M = [ (extend-r {Θ = Θ} ρ) ]r (ι M)
