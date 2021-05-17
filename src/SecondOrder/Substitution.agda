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


--========================================================================================
--∥                              ========================                                ∥
--∥                              ∥  ** DEFINITIONS **  ∥                                ∥
--∥                              ========================                                ∥
--========================================================================================

  --------------------------------------------------------------------------------------------------
  --------------------------------------------------------------
  --          Basic definitions about substitutions           --
  --------------------------------------------------------------

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

  --------------------------------------------------------------------------------------------------
  --------------------------------------------------------
  --          Joins and sums of substitutions           --
  --------------------------------------------------------

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


  --------------------------------------------------------------------------------------------------
  ----------------------------------------------------------------
  --          Action and composition of a substitution          --
  ----------------------------------------------------------------

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


  --------------------------------------------------------------------------------------------------
  ----------------------------------------------------
  --          Interactions with renamings           --
  ----------------------------------------------------

    -- renaming as a substitution

    _ʳ⃗ˢ : ∀ {Γ Δ} → Γ ⇒ʳ Δ → Θ ⊕ Γ ⇒ˢ Δ
    (ρ ʳ⃗ˢ) x = tm-var (ρ x)


    -- action of a substitution on a renaming
    _ˢ∘ʳ_ : ∀ {Γ Δ Ξ} → Θ ⊕ Δ ⇒ˢ Ξ → Γ ⇒ʳ Δ → Θ ⊕ Γ ⇒ˢ Ξ
    σ ˢ∘ʳ ρ = σ ∘ˢ ρ ʳ⃗ˢ

    -- action of a renaming on a substitution
    _ʳ∘ˢ_ : ∀ {Γ Δ Ξ} → Δ ⇒ʳ Ξ → Θ ⊕ Γ ⇒ˢ Δ → Θ ⊕ Γ ⇒ˢ Ξ
    ρ ʳ∘ˢ σ = (ρ ʳ⃗ˢ) ∘ˢ σ

    -- syntactic equality of substitutions
    _≈ˢ_ : ∀ {Γ Δ} (σ τ : Θ ⊕ Γ ⇒ˢ Δ) → Set (lsuc (ℓs ⊔ ℓo))
    _≈ˢ_ {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≈ τ x


  --------------------------------------------------------------------------------------------------
  ----------------------------------------------------
  --          The setoid of substitutions           --
  ----------------------------------------------------

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


  --------------------------------------------------------------------------------------------------
  ---------------------------------------------------------
  --          Basic lemmas about substitutions           --
  ---------------------------------------------------------

  -- the composition of the substitutions induced by the association renamings
  -- are inverses of each other
  assocˢ∘ˢunassocˢ≈ˢid : ∀ {Θ Γ Δ Ξ} → _≈ˢ_ {Θ} ((rename-assoc {Γ} {Δ} {Ξ} ʳ⃗ˢ) ∘ˢ (rename-unassoc ʳ⃗ˢ)) idˢ
  assocˢ∘ˢunassocˢ≈ˢid x = ≈-≡ (cong tm-var (rename-assoc-inv x))

  unassocˢ∘ˢassocˢ≈ˢid : ∀ {Θ Γ Δ Ξ} → _≈ˢ_ {Θ} ((rename-unassoc {Γ} {Δ} {Ξ} ʳ⃗ˢ) ∘ˢ (rename-assoc ʳ⃗ˢ)) idˢ
  unassocˢ∘ˢassocˢ≈ˢid x = ≈-≡ (cong tm-var (rename-unassoc-inv x))



  -- the weakening of equal substitutions are equal
  ≈ˢextendˢ : ∀ {Θ Γ Δ Ξ} {σ τ : Θ ⊕ Γ ⇒ˢ Δ}
        → σ ≈ˢ τ → ⇑ˢ {Ξ = Ξ} σ ≈ˢ ⇑ˢ τ
  ≈ˢextendˢ p (var-inl x) = ≈-tm-ʳ (p x)
  ≈ˢextendˢ p (var-inr x) = ≈-refl

  -- extending a renaming then changing it into a substitution is like
  -- changing it into a substitution and then weaken the result
  extend-weaken : ∀ {Θ Γ Δ Ξ} (ρ : Γ ⇒ʳ Δ) → _≈ˢ_ {Θ = Θ} ((extendʳ ρ) ʳ⃗ˢ) (⇑ˢ {Ξ = Ξ} (ρ ʳ⃗ˢ))
  extend-weaken ρ (var-inl x) = ≈-refl
  extend-weaken ρ (var-inr x) = ≈-refl



  --------------------------------------------------------------------------------------------------
  --------------------------------------------------------------
  --          Lemmas about actions of substitutions           --
  --------------------------------------------------------------

  -- (the main lemmas are marked with **_**, the others are mostly
  -- auxiliary lemmas used to prove the main ones)

  -- ** Two equal substitution have the same action **
  ≈ˢ[]ˢ : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Θ ⊕ Γ ⇒ˢ Δ}
        → σ ≈ˢ τ → [ σ ]ˢ t ≈ [ τ ]ˢ t
  ≈ˢ[]ˢ {t = tm-var x} p = p x
  ≈ˢ[]ˢ {t = tm-meta M ts} p = ≈-meta λ i → ≈ˢ[]ˢ {t = ts i} p
  ≈ˢ[]ˢ {t = tm-oper f es} p = ≈-oper λ i → ≈ˢ[]ˢ {t = es i} (≈ˢextendˢ p)



  -- ** The action of the induced substitution of a renaming is the action of the renaming **
  _ʳ⃗ˢcorrect : ∀ {Θ Γ Δ A} (ρ : Γ ⇒ʳ Δ) (t : Term Θ Γ A) → [ ρ ʳ⃗ˢ ]ˢ t ≈ [ ρ ]ʳ t
  (ρ ʳ⃗ˢcorrect) (tm-var x) = ≈-≡ refl
  (ρ ʳ⃗ˢcorrect) (tm-meta M ts) = ≈-meta λ i → (ρ ʳ⃗ˢcorrect) (ts i)
  (ρ ʳ⃗ˢcorrect) (tm-oper f es) = ≈-oper (λ i → ≈-sym
                                                (≈-trans
                                                  (≈-sym (((extendʳ ρ) ʳ⃗ˢcorrect) (es i)))
                                                  (≈ˢ[]ˢ {t = es i} (extend-weaken ρ))))

  -- action of inl substitution is the same as induced action of inl renaming
  -- (useful particula case of the lemma above)
  inlʳ⃗ˢ≈ˢinlˢ : ∀ {Θ Γ Δ} → inlˢ {Θ} {Γ} {Δ} ≈ˢ ( inlʳ ʳ⃗ˢ )
  inlʳ⃗ˢ≈ˢinlˢ x = ≈-refl



  -- the action of the substitution induced by the inl renaming is the same
  -- as the action of the inl substitution
  -- (useful particular case of the lemma above)
  inl-invariance : ∀ {Θ Γ Δ A} (t : Term Θ Γ A) → [ inlˢ {Θ} {Γ} {Δ} ]ˢ t ≈ [ var-inl ]ʳ t
  inl-invariance = inlʳ ʳ⃗ˢcorrect

  -- same for inr
  inr-invariance : ∀ {Θ Γ Δ A} (t : Term Θ Δ A) → [ inrˢ {Θ} {Γ} {Δ} ]ˢ t ≈ [ var-inr ]ʳ t
  inr-invariance = inrʳ ʳ⃗ˢcorrect


  -- the join "preserves" composition of substitutions
  extend-⋈ˢ : ∀ {Θ Γ Δ Ξ Λ A} (σ : Θ ⊕ Δ ⇒ˢ Ξ) (ρ : Γ ⇒ʳ Δ) (x : A ∈ (Γ ,, Λ))
              → ((λ y → [ var-inl ]ʳ (σ ˢ∘ʳ ρ) y) ⋈ˢ (λ y → tm-var (var-inr y))) x
                 ≈ ((λ y → [ var-inl ]ʳ σ y) ⋈ˢ (λ y → tm-var (var-inr y))) (extendʳ ρ x)
  extend-⋈ˢ σ ρ (var-inl x) = ≈-≡ refl
  extend-⋈ˢ σ ρ (var-inr x) = ≈-≡ refl


  -- ** Composition of a renaming and a substitution extended to terms **
  -- is like composing the actions of the renaming and the substitution
  ˢ∘ʳtm-≈ : ∀ {Θ Γ Δ Ξ A} (σ : Θ ⊕ Δ ⇒ˢ Ξ) (ρ : Γ ⇒ʳ Δ) (t : Term Θ Γ A)
    → [ σ ˢ∘ʳ ρ ]ˢ  t ≈ [ σ ]ˢ ([ ρ ]ʳ t)
  ˢ∘ʳtm-≈ σ ρ (tm-var x) = ≈-≡ refl
  ˢ∘ʳtm-≈ σ ρ (tm-meta M ts) = ≈-meta λ i → ˢ∘ʳtm-≈ σ ρ (ts i)
  ˢ∘ʳtm-≈ σ ρ (tm-oper f es) = ≈-oper (λ i → ˢ∘ʳtm-≈-aux σ ρ (es i))
    where
    ˢ∘ʳtm-≈-aux : ∀ {Θ Γ Δ Ξ Λ A} (σ : Θ ⊕ Δ ⇒ˢ Ξ) (ρ : Γ ⇒ʳ Δ) (t : Term Θ (Γ ,, Λ) A)
                → [ ⇑ˢ (σ ˢ∘ʳ ρ) ]ˢ t ≈ [ ⇑ˢ σ ]ˢ ([ extendʳ ρ ]ʳ t)
    ˢ∘ʳtm-≈-aux σ ρ (tm-var (var-inl x)) = ≈-refl
    ˢ∘ʳtm-≈-aux σ ρ (tm-var (var-inr x)) = ≈-refl
    ˢ∘ʳtm-≈-aux σ ρ (tm-meta M ts) = ≈-meta λ i → ˢ∘ʳtm-≈-aux σ ρ (ts i)
    ˢ∘ʳtm-≈-aux σ ρ (tm-oper f es) = ≈-oper λ i → ≈-trans
                                                   (≈ˢ[]ˢ {t = es i} (≈ˢextendˢ λ x → extend-⋈ˢ σ ρ x))
                                                   (ˢ∘ʳtm-≈-aux (⇑ˢ σ) (extendʳ ρ) (es i))




  -- ** Composition of a substitution and a renaming extended to terms **
  -- is like composing the actions of the substitution and the renaming
  ʳ∘ˢtm-≈ : ∀ {Θ Γ Δ Ξ A} (ρ : Δ ⇒ʳ Ξ) (σ : Θ ⊕ Γ ⇒ˢ Δ) (t : Term Θ Γ A)
    → [ ρ ʳ∘ˢ σ ]ˢ  t ≈ [ ρ ]ʳ ([ σ ]ˢ t)
  ʳ∘ˢtm-≈ ρ σ (tm-var var-slot) = (ρ ʳ⃗ˢcorrect) (σ var-slot)
  ʳ∘ˢtm-≈ ρ σ (tm-var (var-inl x)) = (ρ ʳ⃗ˢcorrect) (σ (var-inl x))
  ʳ∘ˢtm-≈ ρ σ (tm-var (var-inr x)) = (ρ ʳ⃗ˢcorrect) (σ (var-inr x))
  ʳ∘ˢtm-≈ ρ σ (tm-meta M ts) = ≈-meta λ i → ʳ∘ˢtm-≈ ρ σ (ts i)
  ʳ∘ˢtm-≈ ρ σ (tm-oper f es) = ≈-oper (λ i → ʳ∘ˢtm-≈-aux ρ σ (es i))
    where
       -- a lot of auxiliary functions that explain
       -- why things behave well with extensions is this case
       ʳ∘ˢtm-≈-aux₁ : ∀ {Γ Δ Ξ} (ρ : Γ ⇒ʳ Δ) →
                    ((var-inl {Δ = Ξ}) ∘ʳ ρ) ≡ʳ (extendʳ ρ) ∘ʳ (var-inl)
       ʳ∘ˢtm-≈-aux₁ ρ x = refl

       ʳ∘ˢtm-≈-aux₂ : ∀ {Γ Δ Ξ Λ Θ} (ρ : Δ ⇒ʳ Ξ) (σ : Θ ⊕ Γ ⇒ˢ Δ)
                    → (λ {A} (x : A ∈ Γ) → (⇑ˢ {Ξ = Λ} (ρ ʳ∘ˢ σ)) (var-inl x)) ≈ˢ (λ {A} (x : A ∈ Γ)
                    → [ extendʳ ρ ]ʳ (⇑ˢ σ (var-inl x)))
       ʳ∘ˢtm-≈-aux₂ ρ σ x = ≈-trans
                            (≈-trans
                              (≈-tm-ʳ ((ρ ʳ⃗ˢcorrect) (σ x)))
                              (≈-trans
                                (≈-sym (∘r-≈ (σ x) ρ var-inl))
                                (≈ʳ[]ʳ (ʳ∘ˢtm-≈-aux₁ ρ))))
                            (∘r-≈ (σ x) var-inl (extendʳ ρ))


       ʳ∘ˢtm-≈-aux₃ : ∀ {Θ Γ Δ Ξ Λ} (ρ : Δ ⇒ʳ Ξ) (σ : Θ ⊕ Γ ⇒ˢ Δ)
                      →   (λ {A} x → (_⋈ˢ_ {Γ = Γ} {Δ = Λ} (λ x₁ → [ var-inl ]ʳ (ρ ʳ∘ˢ σ) x₁) (λ y → tm-var (var-inr y))) x)
                           ≈ˢ (λ {A} x → [ extendʳ ρ ʳ⃗ˢ ]ˢ ((λ x₁ → [ var-inl ]ʳ σ x₁) ⋈ˢ (λ y → tm-var (var-inr y))) x)
       ʳ∘ˢtm-≈-aux₃ ρ σ (var-inl x) = ≈-trans
                                      (≈-tm-ʳ ((ρ ʳ⃗ˢcorrect) (σ x)))
                                      (≈-trans
                                        (≈-sym (∘r-≈ (σ x) ρ var-inl))
                                        (≈-trans
                                          (≈ʳ[]ʳ (ʳ∘ˢtm-≈-aux₁ ρ))
                                          (≈-trans
                                            (≈-trans
                                              (≈ʳ[]ʳ (ʳ∘ˢtm-≈-aux₁ ρ))
                                              (∘r-≈ (σ x) var-inl (extendʳ ρ)))
                                            (≈-sym ((extendʳ ρ ʳ⃗ˢcorrect) ([ var-inl ]ʳ σ x))))))
       ʳ∘ˢtm-≈-aux₃ ρ σ (var-inr x) = ≈-refl

       -- main auxiliary function here
       ʳ∘ˢtm-≈-aux : ∀ {Θ Γ Δ Ξ Λ A} (ρ : Δ ⇒ʳ Ξ) (σ : Θ ⊕ Γ ⇒ˢ Δ) (t : Term Θ (Γ ,, Λ) A)
                → [ ⇑ˢ (ρ ʳ∘ˢ σ) ]ˢ t ≈ [ extendʳ ρ ]ʳ ([ ⇑ˢ σ ]ˢ t)
       ʳ∘ˢtm-≈-aux ρ σ (tm-var (var-inl x)) = ʳ∘ˢtm-≈-aux₂ ρ σ x
       ʳ∘ˢtm-≈-aux ρ σ (tm-var (var-inr x)) = ≈-refl
       ʳ∘ˢtm-≈-aux ρ σ (tm-meta M ts) = ≈-meta λ i → ʳ∘ˢtm-≈-aux ρ σ (ts i)
       ʳ∘ˢtm-≈-aux ρ σ (tm-oper f es) = ≈-oper (λ i →
                                        ≈-trans
                                          (≈ˢ[]ˢ {t = es i} (≈ˢextendˢ (ʳ∘ˢtm-≈-aux₃ ρ σ)))
                                          (ʳ∘ˢtm-≈-aux (extendʳ ρ) (⇑ˢ σ) (es i)))


  -- interactions between extension and weakening
  extendʳ⇑ˢ : ∀ {Θ Γ Δ Ξ Λ A} (t : Term Θ (Γ ,, Λ) A) (σ : Θ ⊕ Γ ⇒ˢ Δ)
            → [ extendʳ (var-inl {Δ = Ξ}) ]ʳ ([ ⇑ˢ σ ]ˢ t)
             ≈ [ ⇑ˢ ((λ y → [ var-inl ]ʳ σ y) ⋈ˢ (λ y → tm-var (var-inr y))) ]ˢ ([ extendʳ var-inl ]ʳ t)
  extendʳ⇑ˢ {Δ = Δ} {Ξ = Ξ} t σ = ≈-trans
                                  (≈-sym (ʳ∘ˢtm-≈ (extendʳ (var-inl {Δ = Ξ})) ( ⇑ˢ σ) t))
                                  (≈-trans
                                    (≈ˢ[]ˢ
                                      {t = t}
                                      {σ = extendʳ var-inl ʳ∘ˢ ⇑ˢ σ}
                                      {τ = ⇑ˢ ((λ y → [ var-inl ]ʳ σ y) ⋈ˢ (λ y → tm-var (var-inr y))) ˢ∘ʳ extendʳ var-inl}
                                      (extendʳ⇑ˢ-aux σ))
                                    (ˢ∘ʳtm-≈ (⇑ˢ ((λ y → [ var-inl ]ʳ σ y) ⋈ˢ (λ y → tm-var (var-inr y)))) (extendʳ var-inl) t))
            where
              extendʳ⇑ˢ-aux : ∀ {Θ Γ Δ Ξ Λ} (σ : Θ ⊕ Γ ⇒ˢ Δ)
                             → (extendʳ (var-inl {Δ = Ξ}) {Ξ = Λ} ʳ∘ˢ ⇑ˢ σ)
                               ≈ˢ (⇑ˢ ((λ y → [ var-inl ]ʳ σ y) ⋈ˢ (λ y → tm-var (var-inr y))) ˢ∘ʳ extendʳ var-inl)
              extendʳ⇑ˢ-aux σ (var-inl x) =
                                          ≈-trans
                                           (≈-trans
                                             ((extendʳ var-inl ʳ⃗ˢcorrect) ([ var-inl ]ʳ σ x))
                                             (≈-sym (∘r-≈ (σ x) var-inl (extendʳ var-inl))))
                                          (∘r-≈ (σ x) var-inl var-inl)
              extendʳ⇑ˢ-aux σ (var-inr x) = ≈-refl

  -- ** The extension of a composition is equal to the composition of extensions **
  -- we need this lemma to show that the action of substitutions is functorial
  ∘ˢ-≈-extendˢ : ∀ {Θ Γ Δ Λ Ξ} (τ : Θ ⊕ Γ ⇒ˢ Δ) (σ : Θ ⊕ Δ ⇒ˢ Λ)
        →  ⇑ˢ {Ξ = Ξ} (σ ∘ˢ τ) ≈ˢ ((⇑ˢ σ) ∘ˢ (⇑ˢ τ))
  ∘ˢ-≈-extendˢ τ σ (var-inl x) = ∘ˢ-≈-extendˢ-aux (τ x) σ
    where
      ∘ˢ-≈-extendˢ-aux : ∀ {Θ Γ Δ Ξ A} (t : Term Θ Γ A) (σ : Θ ⊕ Γ ⇒ˢ Δ)
        → [ var-inl {Δ = Ξ} ]ʳ ([ σ ]ˢ t)
         ≈ [ (λ x → [ var-inl ]ʳ σ x) ⋈ˢ (λ y → tm-var (var-inr y)) ]ˢ ([ var-inl ]ʳ t)
      ∘ˢ-≈-extendˢ-aux (tm-var x) σ = ≈-refl
      ∘ˢ-≈-extendˢ-aux (tm-meta M ts) σ = ≈-meta λ i → ∘ˢ-≈-extendˢ-aux (ts i) σ
      ∘ˢ-≈-extendˢ-aux (tm-oper f es) σ = ≈-oper (λ i → extendʳ⇑ˢ (es i) σ)
  ∘ˢ-≈-extendˢ τ σ (var-inr x) = ≈-≡ refl


  -- ** Action of substitution is functorial **
  ∘ˢ-≈ : ∀ {Θ Γ Δ Ξ A} (t : Term Θ Γ A) (σ : Θ ⊕ Γ ⇒ˢ Δ) (τ : Θ ⊕ Δ ⇒ˢ Ξ)
        → [ τ ∘ˢ σ ]ˢ t ≈ [ τ ]ˢ ([ σ ]ˢ t)
  ∘ˢ-≈ (tm-var x) σ τ = ≈-refl
  ∘ˢ-≈ (tm-meta M ts) σ τ = ≈-meta (λ i → ∘ˢ-≈ (ts i) σ τ)
  ∘ˢ-≈ (tm-oper f es) σ τ = ≈-oper λ i → ≈-trans
                                           (≈ˢ[]ˢ  {t = es i} (∘ˢ-≈-extendˢ σ τ))
                                           (∘ˢ-≈ (es i) (⇑ˢ σ) (⇑ˢ τ))


  -- the extension of the identity substitution is the identity
  idˢextendˢ : ∀ {Θ Γ Ξ} → _≈ˢ_ {Θ = Θ} (⇑ˢ  {Ξ = Ξ} (idˢ {Γ = Γ})) idˢ
  idˢextendˢ (var-inl x) = ≈-refl
  idˢextendˢ (var-inr x) = ≈-refl

  -- ** The action of the identity substitution is the identity **
  []ˢidˢ : ∀ {Θ Γ A} (t : Term Θ Γ A)
          → [ idˢ ]ˢ t ≈ t
  []ˢidˢ (tm-var x) = ≈-refl
  []ˢidˢ (tm-meta M ts) = ≈-meta λ i → []ˢidˢ (ts i)
  []ˢidˢ (tm-oper f es) = ≈-oper λ i → ≈-trans
                                         (≈ˢ[]ˢ {t = es i} idˢextendˢ)
                                         ([]ˢidˢ (es i))


  -- ** Substitutions preserve syntactical equality of terms **
  ≈-tm-ˢ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {σ : Θ ⊕ Γ ⇒ˢ Δ}
        → s ≈ t → [ σ ]ˢ s ≈ [ σ ]ˢ t
  ≈-tm-ˢ (≈-≡ refl) = ≈-≡ refl
  ≈-tm-ˢ (≈-meta ξ) = ≈-meta (λ i → ≈-tm-ˢ (ξ i))
  ≈-tm-ˢ (≈-oper ξ) = ≈-oper (λ i → ≈-tm-ˢ (ξ i))




  --------------------------------------------------------------------------------------------------
  -------------------------------------------
  --          Lemmas about joins           --
  -------------------------------------------

  -- joins of substitutions give the coproduct structure of Contexts
  -- this is analogous to renamings

  -- existence:
  exist⋈ˢ-l : ∀ {Θ Γ Δ Ξ} {σ : Θ ⊕ Γ ⇒ˢ Ξ} {τ : Θ ⊕ Δ ⇒ˢ Ξ}
          → (σ ⋈ˢ τ) ∘ˢ inlˢ ≈ˢ σ
  exist⋈ˢ-l x = ≈-refl

  exist⋈ˢ-r : ∀ {Θ Γ Μ Ξ} {σ : Θ ⊕ Γ ⇒ˢ Ξ} {τ : Θ ⊕ Μ ⇒ˢ Ξ}
          → σ ⋈ˢ τ ∘ˢ inrˢ ≈ˢ τ
  exist⋈ˢ-r x = ≈-refl

  -- Uniqueness:
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


  -- (6) the join of two substitutions preserves equality of substitutions
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

  --------------------------------------------------------------------------------------------------
  -------------------------------------------
  --          Lemmas about sums            --
  -------------------------------------------

  -- Sums of substitutions have the structure of coproducts

  -- existence:
  exist+ˢ-l : ∀ {Θ Γ Γ' Δ Δ'} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Γ' ⇒ˢ Δ'}
            → σ +ˢ τ ∘ˢ inlˢ ≈ˢ inlˢ ∘ˢ σ
  exist+ˢ-l {σ = σ} {τ = τ} x = ≈-sym (inl-invariance (σ x))

  exist+ˢ-r : ∀ {Θ Γ Γ' Δ Δ'} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Γ' ⇒ˢ Δ'}
            → σ +ˢ τ ∘ˢ inrˢ ≈ˢ inrˢ ∘ˢ τ
  exist+ˢ-r {σ = σ} {τ = τ} y = ≈-sym (inr-invariance (τ y))

  -- uniqueness:
  unique+ˢ : ∀ {Θ Γ Γ' Δ Δ'} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Γ' ⇒ˢ Δ'} {μ ν : Θ ⊕ (Γ ,, Γ') ⇒ˢ (Δ ,, Δ')}
    → μ ∘ˢ inlˢ ≈ˢ inlˢ ∘ˢ σ → μ ∘ˢ inrˢ ≈ˢ inrˢ ∘ˢ τ
    → ν ∘ˢ inlˢ ≈ˢ inlˢ ∘ˢ σ → ν ∘ˢ inrˢ ≈ˢ inrˢ ∘ˢ τ
    → μ ≈ˢ ν
  unique+ˢ {σ = σ} {τ = τ} {μ = μ} {ν = ν} eq_lft1 eq_rgt1 eq_lft2 eq_rgt2 =
    unique-cotupleˢ {σ = inlˢ ∘ˢ σ} {τ = inrˢ ∘ˢ τ} {μ = μ} {ν = ν} eq_lft1 eq_rgt1 eq_lft2 eq_rgt2

  unique+ˢ-aux : ∀ {Θ Γ Γ' Δ Δ'} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Γ' ⇒ˢ Δ'} {μ : Θ ⊕ (Γ ,, Γ') ⇒ˢ (Δ ,, Δ')}
    → μ ∘ˢ inlˢ ≈ˢ inlˢ ∘ˢ σ → μ ∘ˢ inrˢ ≈ˢ inrˢ ∘ˢ τ
    → μ ≈ˢ (σ +ˢ τ)
  unique+ˢ-aux {Θ = Θ} {σ = σ} {τ = τ} {μ = μ} eq_l eq_r =
    unique+ˢ {σ = σ} {τ = τ} {μ = μ} {ν = σ +ˢ τ}
      eq_l eq_r (exist+ˢ-l {σ = σ} {τ = τ}) (exist+ˢ-r {σ = σ} {τ = τ})

  -- sum of substitutions is associative
  +ˢ-assoc-l : ∀ {Θ Γ Γ' Γ'' Δ Δ' Δ''} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Γ' ⇒ˢ Δ'} {γ : Θ ⊕ Γ'' ⇒ˢ Δ''}
           → (σ +ˢ (τ +ˢ γ)) ≈ˢ (rename-unassoc ʳ⃗ˢ) ∘ˢ (σ +ˢ τ) +ˢ γ ∘ˢ (rename-assoc ʳ⃗ˢ)
  +ˢ-assoc-l {σ = σ} {τ = τ} {γ = γ} = ≈ˢ-sym (
    unique+ˢ-aux {σ = σ} {τ = τ +ˢ γ} {μ = (rename-unassoc ʳ⃗ˢ) ∘ˢ (σ +ˢ τ) +ˢ γ ∘ˢ (rename-assoc ʳ⃗ˢ)}
      (λ x →
        ≈-trans
          (≈-tm-ˢ {s = [ var-inl ]ʳ ([ var-inl ]ʳ σ x)} (≈-sym (∘r-≈ (σ x) var-inl var-inl)))
          (≈-trans ((rename-unassoc  ʳ⃗ˢcorrect) ([ var-inl ∘ʳ var-inl ]ʳ σ x))
            (≈-trans
              (≈-trans
                (≈-sym (∘r-≈ (σ x) (var-inl ∘ʳ var-inl) rename-unassoc))
                (≈ʳ[]ʳ λ y → refl))
              (≈-sym ((var-inl ʳ⃗ˢcorrect) (σ x))))))
      λ x → ≈-trans
        (≈-tm-ˢ
          {s =  ((λ x₁ → [ var-inl ]ʳ  ((λ x₂ → [ var-inl ]ʳ σ x₂) ⋈ˢ (λ y → [ var-inr ]ʳ τ y)) x₁) ⋈ˢ (λ y → [ var-inr ]ʳ γ y)) (rename-assoc (var-inr x))}
          {σ = (λ x₁ → tm-var (rename-unassoc x₁)) } {!!})
        {!!})

  -- other direction
  +ˢ-assoc-r : ∀ {Θ Γ Γ' Γ'' Δ Δ' Δ''} {σ : Θ ⊕ Γ ⇒ˢ Δ} {τ : Θ ⊕ Γ' ⇒ˢ Δ'} {γ : Θ ⊕ Γ'' ⇒ˢ Δ''}
             → (σ +ˢ τ) +ˢ γ  ≈ˢ (rename-assoc ʳ⃗ˢ) ∘ˢ (σ +ˢ (τ +ˢ γ)) ∘ˢ (rename-unassoc ʳ⃗ˢ)
  +ˢ-assoc-r {σ = σ} {τ = τ} {γ = γ} = ≈ˢ-sym
             (unique+ˢ-aux {σ = σ +ˢ τ} {τ = γ} {μ = (rename-assoc ʳ⃗ˢ) ∘ˢ (σ +ˢ (τ +ˢ γ)) ∘ˢ (rename-unassoc ʳ⃗ˢ)}
               {!!}
               λ x → ≈-trans
                 ((rename-assoc ʳ⃗ˢcorrect) ([ var-inr ]ʳ ([ var-inr ]ʳ γ x)))
                 ((≈-trans
                   (≈-sym (∘r-≈ ([ var-inr ]ʳ γ x) var-inr rename-assoc))
                   (≈-trans
                     (≈-sym (∘r-≈ (γ x) var-inr (rename-assoc ∘ʳ var-inr)))
                     (≈-sym (((rename-assoc ∘ʳ (var-inr ∘ʳ var-inr)) ʳ⃗ˢcorrect) (γ x)))))))
  --------------------------------------------------------------------------------------------------
