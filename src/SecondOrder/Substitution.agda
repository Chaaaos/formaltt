{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Binary using (Setoid)


import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Renaming
import SecondOrder.Term

module SecondOrder.Substitution
  {ℓs ℓo}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.Renaming Σ


-- ** DEFINITIONS **

  -- substitution

  infix 4 _⊕_⇒ˢ_

  _⊕_⇒ˢ_ : ∀ (Θ : MetaContext) (Γ Δ : Context) → Set (lsuc (ℓs ⊔ ℓo))
  Θ ⊕ Γ ⇒ˢ Δ = ∀ {A} (x : A ∈ Γ) → Term Θ Δ A

  -- identity substitution
  idˢ : ∀ {Θ Γ} → Θ ⊕ Γ ⇒ˢ Γ
  idˢ = tm-var

  -- left and right injections as substitutions
  inlˢ : ∀ {Θ Γ Δ} → Θ ⊕ Γ ⇒ˢ Γ ,, Δ
  inlˢ x = tm-var (var-inl x)

  inrˢ : ∀ {Θ Γ Δ} → Θ ⊕ Δ ⇒ˢ Γ ,, Δ
  inrˢ y = tm-var (var-inr y)

  module _ {Θ : MetaContext}  where

    -- the join of substitutions
    infixl 7 _⋈ˢ_

    _⋈ˢ_ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒ˢ Ξ → Θ ⊕ Δ ⇒ˢ Ξ → Θ ⊕ Γ ,, Δ ⇒ˢ Ξ
    (σ ⋈ˢ τ) (var-inl x) = σ x
    (σ ⋈ˢ τ) (var-inr y) = τ y

    -- the sum of substitutions

    infixl 8 _+ˢ_

    _+ˢ_ : ∀ {Γ Γ' Δ Δ'} → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ Γ' ⇒ˢ Δ' → Θ ⊕ (Γ ,, Γ') ⇒ˢ Δ ,, Δ'
    σ +ˢ τ = (λ x → [ var-inl ]ʳ (σ x)) ⋈ˢ (λ y → [ var-inr ]ʳ (τ y))

    -- renaming as a substitution

    _ʳ⃗ˢ : ∀ {Γ Δ} → Γ ⇒ʳ Δ → Θ ⊕ Γ ⇒ˢ Δ
    (ρ ʳ⃗ˢ) x = tm-var (ρ x)

    -- extending a substitution

    ⇑ˢ : ∀ {Γ Δ Ξ} → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ (Γ ,, Ξ) ⇒ˢ (Δ ,, Ξ)
    ⇑ˢ σ = σ +ˢ idˢ

    -- the action of a substitution on a term (contravariant)
    infixr 6 [_]ˢ_

    [_]ˢ_ : ∀ {Γ Δ : Context} {A : sort} → Θ ⊕ Γ ⇒ˢ Δ → Term Θ Γ A → Term Θ Δ A
    [ σ ]ˢ (tm-var x) = σ x
    [ σ ]ˢ (tm-meta M ts) = tm-meta M (λ i → [ σ ]ˢ ts i)
    [ σ ]ˢ (tm-oper f es) = tm-oper f (λ i → [ ⇑ˢ σ ]ˢ es i)

    -- composition of substitutions
    infixl 7 _∘ˢ_
    _∘ˢ_ : ∀ {Γ Δ Ξ : Context} → Θ ⊕ Δ ⇒ˢ Ξ → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ Γ ⇒ˢ Ξ
    (σ ∘ˢ τ) x = [ σ ]ˢ τ x

    -- action of a substitution on a renaming
    _ˢ∘ʳ_ : ∀ {Γ Δ Ξ} → Θ ⊕ Δ ⇒ˢ Ξ → Γ ⇒ʳ Δ → Θ ⊕ Γ ⇒ˢ Ξ
    σ ˢ∘ʳ ρ = σ ∘ˢ ρ ʳ⃗ˢ

    -- syntactic equality of substitutions
    _≈ˢ_ : ∀ {Γ Δ} (σ τ : Θ ⊕ Γ ⇒ˢ Δ) → Set (lsuc (ℓs ⊔ ℓo))
    _≈ˢ_ {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≈ τ x

    infixl 3 _≈ˢ_

  ≈ˢ-refl : ∀ {Θ Γ Δ} {σ : Θ ⊕ Γ ⇒ˢ Δ}
          → σ ≈ˢ σ
  ≈ˢ-refl x = ≈-refl
            
  ≈ˢ-sym : ∀ {Θ Γ Δ} {σ τ : Θ ⊕ Γ ⇒ˢ Δ}
          → σ ≈ˢ τ
          → τ ≈ˢ σ
  ≈ˢ-sym eq x = ≈-sym (eq x)
                           
  ≈ˢ-trans : ∀ {Θ Γ Δ} {σ τ μ : Θ ⊕ Γ ⇒ˢ Δ}
           → σ ≈ˢ τ → τ ≈ˢ μ
           → σ ≈ˢ μ
  ≈ˢ-trans eq1 eq2 x = ≈-trans (eq1 x) (eq2 x)
    
  -- substitutions form a setoid
  substitution-setoid : ∀ (Γ Δ : Context) (Θ : MetaContext) → Setoid (lsuc ℓs ⊔ lsuc ℓo) (lsuc ℓs ⊔ lsuc ℓo)
  substitution-setoid Γ Δ Θ =
    record
      { Carrier = Θ ⊕ Γ ⇒ˢ Δ
      ;  _≈_ = λ σ τ → σ ≈ˢ τ
      ; isEquivalence =
                      record
                        { refl = λ {σ} x → ≈ˢ-refl {σ = σ} x
                        ; sym = ≈ˢ-sym
                        ; trans = ≈ˢ-trans
                        }
      }

--========================================================================================
--∥                              ========================                                ∥
--∥                              ∥  ** METATHEOREMS **  ∥                                ∥
--∥                              ========================                                ∥
--========================================================================================

  -------------------------------------------
  --          Lemmas about joins           --
  -------------------------------------------

  -- joins of substitutions give the coproduct structure of Contexts
  -- this is analogous to renamings
  unique⋈ˢ : ∀ {Θ Γ Μ Ξ} {σ : Θ ⊕ Γ ⇒ˢ Ξ} {τ : Θ ⊕ Μ ⇒ˢ Ξ} {μ : Θ ⊕ Γ ,, Μ ⇒ˢ Ξ}
          → (μ ∘ˢ inlˢ) ≈ˢ σ
          → (μ ∘ˢ inrˢ) ≈ˢ τ
          → μ ≈ˢ (σ ⋈ˢ τ)
  unique⋈ˢ eq1 eq2 (var-inl x) = eq1 x
  unique⋈ˢ eq1 eq2 (var-inr y) = eq2 y

  unique-cotupleˢ : ∀ {Θ Γ Γ' Ξ} {σ : Θ ⊕ Γ ⇒ˢ Ξ} {τ : Θ ⊕ Γ' ⇒ˢ Ξ} {μ ν : Θ ⊕ Γ ,, Γ' ⇒ˢ Ξ}
          → (μ ∘ˢ inlˢ) ≈ˢ σ → (μ ∘ˢ inrˢ) ≈ˢ τ
          → (ν ∘ˢ inlˢ) ≈ˢ σ → (ν ∘ˢ inrˢ) ≈ˢ τ
          → μ ≈ˢ ν
  unique-cotupleˢ {μ = μ} {ν = ν} eq1 eq2 eq3 eq4 (var-inl x) = ≈ˢ-trans eq1 (≈ˢ-sym eq3) x
  unique-cotupleˢ {μ = μ} {ν = ν} eq1 eq2 eq3 eq4 (var-inr y) = ≈ˢ-trans eq2 (≈ˢ-sym eq4) y


  --------------------------------------------------------------------------------------------------
  -------------------------------------------
  --          Lemmas about sums            --
  -------------------------------------------

  -- Sums of substitutions have the structure of coproducts
  unique+ˢ : ∀ {Θ Γ Γ' Δ Δ'} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Γ' ⇒ˢ Δ'} {μ ν : Θ ⊕ (Γ ,, Γ') ⇒ˢ (Δ ,, Δ')}
    → μ ∘ˢ inlˢ ≈ˢ inlˢ ∘ˢ σ → μ ∘ˢ inrˢ ≈ˢ inrˢ ∘ˢ τ
    → ν ∘ˢ inlˢ ≈ˢ inlˢ ∘ˢ σ → ν ∘ˢ inrˢ ≈ˢ inrˢ ∘ˢ τ
    → μ ≈ˢ ν
  unique+ˢ {σ = σ} {τ = τ} {μ = μ} {ν = ν} eq_lft1 eq_rgt1 eq_lft2 eq_rgt2 =
    unique-cotupleˢ {σ = inlˢ ∘ˢ σ} {τ = inrˢ ∘ˢ τ} {μ = μ} {ν = ν} eq_lft1 eq_rgt1 eq_lft2 eq_rgt2

  -- (1) the weakening of equal substitutions are equal
  ≈ˢextendˢ : ∀ {Θ Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒ˢ Δ}
        → σ ≈ˢ τ → ⇑ˢ {Ξ = Ξ} σ ≈ˢ ⇑ˢ τ
  ≈ˢextendˢ p (var-inl x) = ≈-tm-ʳ (p x)
  ≈ˢextendˢ p (var-inr x) = ≈-≡ refl

  --------------------------------------------------------------------------------------------------

  -- (2) two equal substitution have the same action
  ≈ˢ[]ˢ : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Θ ⊕ Γ ⇒ˢ Δ}
        → σ ≈ˢ τ → [ σ ]ˢ t ≈ [ τ ]ˢ t
  ≈ˢ[]ˢ {t = tm-var x} p = p x
  ≈ˢ[]ˢ {t = tm-meta M ts} p = ≈-meta λ i → ≈ˢ[]ˢ {t = ts i} p
  ≈ˢ[]ˢ {t = tm-oper f es} p = ≈-oper λ i → ≈ˢ[]ˢ {t = es i} (≈ˢextendˢ p)


  -- (3) composition of substitutions commutes with equality
  -- auxiliary functions :

  -- composition of renamings an substitutions extended to terms
  ˢ∘ʳtm-≈ : ∀ {Θ Γ Δ Ξ A} (σ : Θ ⊕ Δ ⇒ˢ Ξ) (ρ : Γ ⇒ʳ Δ) (t : Term Θ Γ A)
    → [ σ ˢ∘ʳ ρ ]ˢ  t ≈ [ σ ]ˢ ([ ρ ]ʳ t)
  ˢ∘ʳtm-≈ σ ρ (tm-var x) = ≈-≡ refl
  ˢ∘ʳtm-≈ σ ρ (tm-meta M ts) = ≈-meta λ i → ˢ∘ʳtm-≈ σ ρ (ts i)
  ˢ∘ʳtm-≈ σ ρ (tm-oper f es) = ≈-oper (λ i → ˢ∘ʳtm-≈-aux σ ρ (es i)) -- needs an auxiliary function
    where
    ˢ∘ʳtm-≈-aux : ∀ {Θ Γ Δ Ξ Λ A} (σ : Θ ⊕ Δ ⇒ˢ Ξ) (ρ : Γ ⇒ʳ Δ) (t : Term Θ (Γ ,, Λ) A)
                → [ ⇑ˢ (σ ˢ∘ʳ ρ) ]ˢ t ≈ [ ⇑ˢ σ ]ˢ ([ extendʳ ρ ]ʳ t)
    ˢ∘ʳtm-≈-aux σ ρ (tm-var x) = ≈-≡ {!!}
    ˢ∘ʳtm-≈-aux σ ρ (tm-meta M ts) = {!!}
    ˢ∘ʳtm-≈-aux σ ρ (tm-oper f es) = {!!}
  -- ˢ∘ʳtm-≈ σ ρ (SecondOrder.Term.tm-oper f es) = ≈-oper (λ i → {!!})

  -- interactions between extension and weakening
  extendʳ⇑ˢ : ∀ {Θ Γ Δ Ξ Λ A} (t : Term Θ (Γ ,, Λ) A) (σ : Θ ⊕ Γ ⇒ˢ Δ)
            → [ extendʳ (var-inl {Δ = Ξ}) ]ʳ ([ ⇑ˢ σ ]ˢ t)
             ≈ [ ⇑ˢ ((λ y → [ var-inl ]ʳ σ y) ⋈ˢ (λ y → tm-var (var-inr y))) ]ˢ ([ extendʳ var-inl ]ʳ t)
  extendʳ⇑ˢ {Δ = Δ} {Ξ = Ξ} t σ = ≈-trans
                                  (≈-sym {!!}) -- define the action of a renaming on a substitutions, show things on this
                                  (≈-trans
                                    {!!}
                                    (ˢ∘ʳtm-≈ ( ⇑ˢ ((λ y → [ var-inl ]ʳ σ y) ⋈ˢ (λ y → tm-var (var-inr y)))) (extendʳ var-inl) t))


  -- The extension of a composition is equal to the composition of extensions
  -- We need this lemma to show substitutions act functorially on terms
  ∘ˢ-≈-extendˢ : ∀ {Θ Γ Δ Λ Ξ} (τ : Θ ⊕ Γ ⇒ˢ Δ) (σ : Θ ⊕ Δ ⇒ˢ Λ)
        →  ⇑ˢ {Ξ = Ξ} (σ ∘ˢ τ) ≈ˢ ((⇑ˢ σ) ∘ˢ (⇑ˢ τ))
  ∘ˢ-≈-extendˢ τ σ (var-inl x) = ∘ˢ-≈-extendˢ-aux (τ x) σ
    where
      ∘ˢ-≈-extendˢ-aux : ∀ {Θ Γ Δ Ξ A} (t : Term Θ Γ A) (σ : Θ ⊕ Γ ⇒ˢ Δ)
        → [ var-inl {Δ = Ξ} ]ʳ ([ σ ]ˢ t)
         ≈ [ (λ x → [ var-inl ]ʳ σ x) ⋈ˢ (λ y → tm-var (var-inr y)) ]ˢ ([ var-inl ]ʳ t)
      ∘ˢ-≈-extendˢ-aux (tm-var x) σ = ≈-≡ refl
      ∘ˢ-≈-extendˢ-aux (tm-meta M ts) σ = ≈-meta λ i → ∘ˢ-≈-extendˢ-aux (ts i) σ
      ∘ˢ-≈-extendˢ-aux (tm-oper f es) σ = ≈-oper (λ i → extendʳ⇑ˢ (es i) σ)
  ∘ˢ-≈-extendˢ τ σ (var-inr x) = ≈-≡ refl


  -- (3) Substitutions act functorially on terms
  ∘ˢ-≈ : ∀ {Θ Γ Δ Ξ A} (t : Term Θ Γ A) (σ : Θ ⊕ Γ ⇒ˢ Δ) (τ : Θ ⊕ Δ ⇒ˢ Ξ)
        → [ τ ∘ˢ σ ]ˢ t ≈ [ τ ]ˢ ([ σ ]ˢ t)
  ∘ˢ-≈ (tm-var x) σ τ = ≈-≡ refl
  ∘ˢ-≈ (tm-meta M ts) σ τ = ≈-meta (λ i → ∘ˢ-≈ (ts i) σ τ)
  ∘ˢ-≈ (tm-oper f es) σ τ = ≈-oper λ i → ≈-trans
                                           (≈ˢ[]ˢ  {t = es i} (∘ˢ-≈-extendˢ σ τ))
                                           (∘ˢ-≈ (es i) (⇑ˢ σ) (⇑ˢ τ))


  -- (4) the action of the identity substitution is the identity
  idˢextendˢ : ∀ {Θ Γ Ξ} → _≈ˢ_ {Θ = Θ} (⇑ˢ  {Ξ = Ξ} (idˢ {Γ = Γ})) idˢ
  idˢextendˢ (var-inl x) = ≈-≡ refl
  idˢextendˢ (var-inr x) = ≈-≡ refl

  -- (4)
  []ˢidˢ : ∀ {Θ Γ A} (t : Term Θ Γ A)
          → [ idˢ ]ˢ t ≈ t
  []ˢidˢ (tm-var x) = ≈-≡ refl
  []ˢidˢ (tm-meta M ts) = ≈-meta λ i → []ˢidˢ (ts i)
  []ˢidˢ (tm-oper f es) = ≈-oper λ i → ≈-trans
                                         (≈ˢ[]ˢ {t = es i} idˢextendˢ)
                                         ([]ˢidˢ (es i))


  -- (5) substitutions preserve syntactical equality of terms
  ≈-tm-ˢ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {σ : Θ ⊕ Γ ⇒ˢ Δ}
        → s ≈ t → [ σ ]ˢ s ≈ [ σ ]ˢ t
  ≈-tm-ˢ (≈-≡ refl) = ≈-≡ refl
  ≈-tm-ˢ (≈-meta ξ) = ≈-meta (λ i → ≈-tm-ˢ (ξ i))
  ≈-tm-ˢ (≈-oper ξ) = ≈-oper (λ i → ≈-tm-ˢ (ξ i))


  -- (6) the join of two substitutions preserves equality
  ⋈ˢ-≈ˢ-r : ∀ {Θ Γ Δ Ξ} {σ : Θ ⊕ Γ ⇒ˢ Ξ} {τ₁ τ₂ : Θ ⊕ Δ ⇒ˢ Ξ}
    → τ₁ ≈ˢ τ₂ → (σ ⋈ˢ τ₁) ≈ˢ (σ ⋈ˢ τ₂)
  ⋈ˢ-≈ˢ-r p (var-inl x) = ≈-≡ refl
  ⋈ˢ-≈ˢ-r p (var-inr x) = p x

  ⋈ˢ-≈ˢ-l : ∀ {Θ Γ Δ Ξ} {σ₁ σ₂ : Θ ⊕ Γ ⇒ˢ Ξ} {τ : Θ ⊕ Δ ⇒ˢ Ξ}
    → σ₁ ≈ˢ σ₂ → (σ₁ ⋈ˢ τ) ≈ˢ (σ₂ ⋈ˢ τ)
  ⋈ˢ-≈ˢ-l p (var-inl x) = p x
  ⋈ˢ-≈ˢ-l p (var-inr x) = ≈-≡ refl

  ⋈ˢ-≈ˢ : ∀ {Θ Γ Δ Ξ} {σ₁ σ₂ : Θ ⊕ Γ ⇒ˢ Ξ} {τ₁ τ₂ : Θ ⊕ Δ ⇒ˢ Ξ}
    → σ₁ ≈ˢ σ₂ → τ₁ ≈ˢ τ₂ → (σ₁ ⋈ˢ τ₁) ≈ˢ (σ₂ ⋈ˢ τ₂)
  ⋈ˢ-≈ˢ pσ pτ = λ x → ≈-trans (⋈ˢ-≈ˢ-r pτ x) (⋈ˢ-≈ˢ-l pσ x)
