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
  _⊕_⇒ʳ_ : ∀ (Θ : MetaContext) (Γ Δ : Context) → Set ℓs
  Θ ⊕ Γ ⇒ʳ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

  infix 4 _⊕_⇒ʳ_


  module _ {Θ : MetaContext}  where

      -- extending a renaming
      extendʳ : ∀ {Γ Δ} → Θ ⊕ Γ ⇒ʳ Δ → ∀ {Ξ} → Θ ⊕ Γ ,, Ξ ⇒ʳ Δ ,, Ξ
      extendʳ ρ (var-inl x) = var-inl (ρ x)
      extendʳ ρ (var-inr y) = var-inr y

      -- the identity renaming
      idʳ : ∀ {Γ : Context} → Θ ⊕ Γ ⇒ʳ Γ
      idʳ x = x

      -- composition of renamings
      _∘ʳ_ : ∀ {Γ Δ Ξ : Context} → Θ ⊕ Δ ⇒ʳ Ξ → Θ ⊕ Γ ⇒ʳ Δ → Θ ⊕ Γ ⇒ʳ Ξ
      (σ ∘ʳ ρ) x = σ (ρ x)

      infix 7 _∘ʳ_

      -- action of a renaming on terms
      [_]ʳ_ : ∀ {Γ Δ A} → Θ ⊕ Γ ⇒ʳ Δ → Term Θ Γ A → Term Θ Δ A
      [ ρ ]ʳ (tm-var x) = tm-var (ρ x)
      [ ρ ]ʳ (tm-meta M ts) = tm-meta M (λ i → [ ρ ]ʳ (ts i))
      [ ρ ]ʳ (tm-oper f es) = tm-oper f (λ i → [ (extendʳ ρ) ]ʳ (es i))

      infix 6 [_]ʳ_

      -- the reassociation renaming
      rename-assoc-r : ∀ {Γ Δ Ξ} → Θ ⊕ (Γ ,, Δ) ,, Ξ ⇒ʳ Γ ,, (Δ ,, Ξ)
      rename-assoc-r (var-inl (var-inl x)) = var-inl x
      rename-assoc-r (var-inl (var-inr y)) = var-inr (var-inl y)
      rename-assoc-r (var-inr z) = var-inr (var-inr z)

      rename-assoc-l : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ,, (Δ ,, Ξ) ⇒ʳ (Γ ,, Δ) ,, Ξ
      rename-assoc-l (var-inl x) = var-inl (var-inl x)
      rename-assoc-l (var-inr (var-inl y)) = var-inl (var-inr y)
      rename-assoc-l (var-inr (var-inr z)) = var-inr z

      -- apply the reassociation renaming on terms
      term-reassoc : ∀ {Δ Γ Ξ A}
        → Term Θ (Δ ,, (Γ ,, Ξ)) A
        → Term Θ ((Δ ,, Γ) ,, Ξ) A
      term-reassoc = [ rename-assoc-l ]ʳ_

      -- the empty context is the unit
      rename-ctx-empty-r : ∀ {Γ} → Θ ⊕ Γ ,, ctx-empty ⇒ʳ Γ
      rename-ctx-empty-r (var-inl x) = x

      rename-ctx-empty-inv : ∀ {Γ} → Θ ⊕ Γ ⇒ʳ Γ ,, ctx-empty
      rename-ctx-empty-inv x = var-inl x

      -- weakening
      ⇑ʳ : ∀ {Γ Δ A} → Term Θ Γ A → Term Θ (Γ ,, Δ) A
      ⇑ʳ = [ var-inl ]ʳ_

      weakenʳ : ∀ {Γ Δ A} → Term Θ Δ A → Term Θ (Γ ,, Δ) A
      weakenʳ = [ var-inr ]ʳ_

      -- this is probably useless to have a name for
      -- but it allows us to use the extended renaming as a fuction from terms to terms
      app-extendʳ : ∀ {Γ Δ Ξ A} → Θ ⊕ Γ ⇒ʳ Δ → Term Θ (Γ ,, Ξ) A → Term Θ (Δ ,, Ξ) A
      app-extendʳ ρ t = [ extendʳ ρ ]ʳ t



    -- ** Substitutions **

  -- substitition
  _⊕_⇒ˢ_ : ∀ (Θ : MetaContext) (Γ Δ : Context) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
  Θ ⊕ Γ ⇒ˢ Δ = ∀ {A} (x : A ∈ Δ) → Term Θ Γ A

  infix 4 _⊕_⇒ˢ_

  module _ {Θ : MetaContext}  where

      -- extending a substitution
      ⇑ˢ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ (Γ ,, Ξ) ⇒ˢ (Δ ,, Ξ)
      ⇑ˢ {Ξ = Ξ} σ (var-inl x) = ⇑ʳ (σ x)
      ⇑ˢ σ (var-inr x) = tm-var (var-inr x)

      extend-sʳ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ Ξ ,, Γ ⇒ˢ Ξ ,, Δ
      extend-sʳ {Ξ = Ξ} σ (var-inl x) = tm-var (var-inl x)
      extend-sʳ σ (var-inr x) = weakenʳ (σ x)

      -- the action of a substitution on a term (contravariant)
      _[_]ˢ : ∀ {Γ Δ : Context} {A : sort} → Term Θ Δ A → Θ ⊕ Γ ⇒ˢ Δ → Term Θ Γ A
      (tm-var x) [ σ ]ˢ = σ x
      (tm-meta M ts) [ σ ]ˢ = tm-meta M (λ i → (ts i) [ σ ]ˢ)
      (tm-oper f es) [ σ ]ˢ = tm-oper f (λ i → es i [ ⇑ˢ σ ]ˢ)

      infixr 6 _[_]ˢ

      -- identity substitution
      idˢ : ∀ {Γ : Context} → Θ ⊕ Γ ⇒ˢ Γ
      idˢ = tm-var

      -- application of extension
      -- this is probably useless to have a name for, but it does give a way to make a
      -- function to go from Terms to Terms
      app-⇑ˢ : ∀ {Γ Δ Ξ A} → Θ ⊕ Γ ⇒ˢ Δ → Term Θ (Δ ,, Ξ) A → Term Θ (Γ ,, Ξ) A
      app-⇑ˢ σ t = t [ ⇑ˢ σ ]ˢ

      -- composition of substitutions
      _∘ˢ_ : ∀ {Γ Δ Ξ : Context} → Θ ⊕ Δ ⇒ˢ Ξ → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ Γ ⇒ˢ Ξ
      (σ ∘ˢ ρ) x = σ x [ ρ ]ˢ

      infixl 7 _∘ˢ_

      -- action of a renaming on a substitution
      _r∘ˢ_ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒ʳ Δ → Θ ⊕ Ξ ⇒ˢ Δ → Θ ⊕ Ξ ⇒ˢ Γ
      (ρ r∘ˢ σ) x = σ (ρ x)

      -- action of a substitution on a renaming
      _ˢ∘ʳ_ : ∀ {Γ Δ Ξ} → Θ ⊕ Δ ⇒ˢ Γ → Θ ⊕ Δ ⇒ʳ Ξ → Θ ⊕ Ξ ⇒ˢ Γ
      (σ ˢ∘ʳ ρ) x = [ ρ ]ʳ (σ x)



      -- ** Metavariable instantiations **

  -- metavariable instantiation
  _⇒ⁱ_⊕_  : MetaContext → MetaContext → Context → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
  ψ ⇒ⁱ Θ ⊕ Γ = ∀ (M : mv Θ) → Term ψ (Γ ,, mv-arity Θ M) (mv-sort Θ M)

  -- action of a metavariable instantiation on terms
  _[_]ⁱ : ∀ {Γ : Context} {A : sort} {Θ Ψ : MetaContext} {Δ} → Term Θ Γ A → ∀ (I : Ψ ⇒ⁱ Θ ⊕ Δ) → Term Ψ (Δ ,, Γ) A

  []ⁱ-mv : ∀ {Γ : Context} {Θ Ψ : MetaContext} {Δ} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B) (I : Ψ ⇒ⁱ Θ ⊕ Δ) → Ψ ⊕ Δ ,, Γ ⇒ˢ Δ ,, mv-arity Θ M

  []ⁱ-mv M ts I (var-inl x) = tm-var (var-inl x)
  []ⁱ-mv M ts I (var-inr x) =  (ts x) [ I ]ⁱ

  (tm-var x) [ I ]ⁱ = tm-var (var-inr x)
  _[_]ⁱ {Γ = Γ} {Θ = Θ} {Δ = Δ} (tm-meta M ts) I = (I M) [ []ⁱ-mv M ts I ]ˢ
  _[_]ⁱ {Ψ = Ψ} (tm-oper f es) I = tm-oper f (λ i → [ (rename-assoc-l {Θ = Ψ}) ]ʳ (es i [ I ]ⁱ) )

  infixr 6 _[_]ⁱ

  -- the identity metavariable instantiation
  idⁱ : ∀ {Θ} → Θ ⇒ⁱ Θ ⊕ ctx-empty
  idⁱ t = tm-meta t (λ i → weakenʳ (tm-var i))

  idⁱ-inv : ∀ {Θ Γ} → Θ ⊕ (ctx-empty ,, Γ) ⇒ʳ Γ
  idⁱ-inv (var-inr x) = x

  -- composition of metavariable instantiations
  _∘ⁱ_ : ∀ {Θ ψ Ω Γ Δ} → Ω ⇒ⁱ ψ ⊕ Δ → ψ ⇒ⁱ Θ ⊕ Γ → (Ω ⇒ⁱ Θ ⊕ (Δ ,, Γ))
  _∘ⁱ_ {Θ = Θ} {ψ = ψ} {Γ = Γ} {Δ = Δ} μ I = λ M → term-reassoc (I M [ μ ]ⁱ)



    -- ** Interactions **

  -- action of a metavariable instantiation on a substitution
  _M∘ˢ_ : ∀ {Θ ψ Γ Δ Ξ} → ψ ⇒ⁱ Θ ⊕ Ξ → Θ ⊕ Δ ⇒ˢ Γ → ψ ⊕ (Ξ ,, Δ) ⇒ˢ (Ξ ,, Γ)
  (I M∘ˢ σ) (var-inl x) = tm-var (var-inl x)
  (I M∘ˢ σ) (var-inr x) = σ x [ I ]ⁱ

  -- action of a substitution on a metavariable instantiation
  _s∘ⁱ_ : ∀ {Θ ψ Γ Δ} → ψ ⊕ Δ ⇒ˢ Γ → ψ ⇒ⁱ Θ ⊕ Γ → ψ ⇒ⁱ Θ ⊕ Δ
  _s∘ⁱ_ σ I M = I M [ ⇑ˢ σ ]ˢ

  -- action of a renaming on a metavariable instantiation
  _r∘ⁱ_ : ∀ {Θ ψ Δ Ξ} → ψ ⇒ⁱ Θ ⊕ Ξ → Θ ⊕ Ξ ⇒ʳ Δ → ψ ⇒ⁱ Θ ⊕ Δ
  _r∘ⁱ_ {Θ = Θ} I ρ M = [ (extendʳ {Θ = Θ} ρ) ]ʳ (I M)
