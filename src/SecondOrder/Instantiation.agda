open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Renaming
import SecondOrder.Term
import SecondOrder.Substitution

module SecondOrder.Instantiation
  {ℓs ℓo}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.Renaming Σ
  open SecondOrder.Substitution Σ

--========================================================================================
--∥                              ========================                                ∥
--∥                              ∥  ** DEFINITIONS **  ∥                                ∥
--∥                              ========================                                ∥
--========================================================================================


  --------------------------------------------------------------------------------------------------
  ---------------------------------------------------------------
  --          Basic definitions about instantiations           --
  ---------------------------------------------------------------


  -- metavariable instantiation
  _⇒ⁱ_⊕_  : MetaContext → MetaContext → Context → Set (lsuc (ℓs ⊔ ℓo))
  Θ ⇒ⁱ Ξ ⊕ Γ = ∀ (M : mv Θ) → Term Ξ (Γ ,, mv-arity Θ M) (mv-sort Θ M)

  -- the identity metavariable instantiation
  idⁱ : ∀ {Θ} → Θ ⇒ⁱ Θ ⊕ ctx-empty
  idⁱ t = tm-meta t (λ i → [ var-inr ]ʳ (tm-var i))

  -- action of a metavariable instantiation on terms

  infixr 6 [_]ⁱ_

  [_]ⁱ_ : ∀ {Θ Ξ Γ Δ A} → Ξ ⇒ⁱ Θ ⊕ Δ → Term Ξ Γ A → Term Θ (Δ ,, Γ) A
  [ I ]ⁱ (tm-var x) = tm-var (var-inr x)
  [ I ]ⁱ (tm-meta M ts) = [ var-inl ʳ⃗ˢ ⋈ˢ (λ x →  [ I ]ⁱ ts x) ]ˢ I M
  [ I ]ⁱ (tm-oper f es) = tm-oper f λ i → term-reassoc ([ I ]ⁱ es i)

  -- composition of metavariable instantiations
  infixl 5 _∘ⁱ_
  _∘ⁱ_ : ∀ {Θ Ξ Ω Γ Δ} → Ξ ⇒ⁱ Ω ⊕ Δ → Θ ⇒ⁱ Ξ ⊕ Γ → (Θ ⇒ⁱ Ω ⊕ (Δ ,, Γ))
  (I ∘ⁱ J) M =  term-reassoc ([ I ]ⁱ (J M))

  -- syntactic equality of instantiations
  _≈ⁱ_ : ∀ {Θ Ξ Γ} (I J : Θ ⇒ⁱ Ξ ⊕ Γ) → Set (lsuc (ℓs ⊔ ℓo))
  _≈ⁱ_ {Θ} I J = ∀ (M : mv Θ) → I M ≈ J M

  -- as a special case we define instantiation of a closed term such that
  -- the empty context does not appear. This is used when axioms are instantiated.
  instantiate-closed-term : ∀ {Θ Ξ Γ A} (I : Θ ⇒ⁱ Ξ ⊕ Γ) → Term Θ ctx-empty A → Term Ξ Γ A
  instantiate-closed-term I t =  [ ctx-empty-right-unit ]ʳ ([ I ]ⁱ t)


  --------------------------------------------------------------------------------------------------
  ----------------------------------------------------------------------
  --          Interactions with renamings and substitutions           --
  ----------------------------------------------------------------------

  -- action of a renaming on an instantiation
  _ʳ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → Γ ⇒ʳ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (ρ ʳ∘ⁱ I) M = [ (extendʳ ρ) ]ʳ I M

  -- action of a substitution on an instantiation
  _ˢ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → ψ ⊕ Γ ⇒ˢ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (σ ˢ∘ⁱ I) M = [ ⇑ˢ σ ]ˢ I M

  -- action of an instantiation on a substitution
  _ⁱ∘ˢ_ : ∀ {Θ ψ Γ Δ Ξ} → Θ ⇒ⁱ ψ ⊕ Ξ → Θ ⊕ Γ ⇒ˢ Δ → ψ ⊕ Γ ⇒ˢ (Ξ ,, Δ)
  (I ⁱ∘ˢ σ) x = [ I ]ⁱ σ x


--========================================================================================
--∥                              ========================                                ∥
--∥                              ∥  ** METATHEOREMS **  ∥                                ∥
--∥                              ========================                                ∥
--========================================================================================

  --------------------------------------------------------------------------------------------------
  ----------------------------------------------------------
  --          Basic lemmas about instantiations           --
  ----------------------------------------------------------


  -- ** Two equal instantiations have the same action **
  ≈ⁱ[]ⁱ : ∀ {Θ Ω Γ Δ A} {t : Term Θ Δ A} {I J : Θ ⇒ⁱ Ω ⊕ Γ}
        → I ≈ⁱ J → [ I ]ⁱ t ≈ [ J ]ⁱ t
  ≈ⁱ[]ⁱ {t = tm-var x} p = ≈-≡ refl
  ≈ⁱ[]ⁱ {t = tm-meta M ts} {I = I} {J = J} p = ≈-trans
                                               (≈ˢ[]ˢ
                                                 {t = I M}
                                                 {σ = var-inl ʳ⃗ˢ ⋈ˢ (λ x → [ I ]ⁱ ts x)}
                                                 {τ =  var-inl ʳ⃗ˢ ⋈ˢ (λ x → [ J ]ⁱ ts x)}
                                                 (⋈ˢ-≈ˢ-r λ x → ≈ⁱ[]ⁱ {t = ts x} p))
                                               (≈-tm-ˢ (p M))
  ≈ⁱ[]ⁱ {t = tm-oper f es} p = ≈-oper λ i → ≈-tm-ʳ (≈ⁱ[]ⁱ {t = es i} p)


  -- ** Action of instantiation is functirial wrt. composition ** (the proof comes later)
  ∘ⁱ-≈ : ∀ {Θ Ω ψ Γ Δ Ξ A} (t : Term Θ Ξ A) (I : Ω ⇒ⁱ ψ ⊕ Δ) (J : Θ ⇒ⁱ Ω ⊕ Γ)
        → [ I ∘ⁱ J ]ⁱ t ≈ term-reassoc ([ I ]ⁱ ([ J ]ⁱ t))

  -- reassociation of a composition
  reassoc-∘ⁱ : ∀ {Θ Ω ψ Γ Δ Ξ Λ A} (t : Term Θ (Ξ ,, Λ) A) (I : Ω ⇒ⁱ ψ ⊕ Δ) (J : Θ ⇒ⁱ Ω ⊕ Γ)
              → term-reassoc ([ I ∘ⁱ J ]ⁱ t) ≈  term-reassoc (term-reassoc ([ I ]ⁱ ([ J ]ⁱ t)))
  reassoc-∘ⁱ t I J = ≈-tm-ʳ (∘ⁱ-≈ t I J)

  -- auxiliary function, to deal with extensions in the oper case
  ∘ⁱ-≈-oper : ∀ {Θ Ω ψ Γ Δ Ξ Λ A} (t : Term Θ (Ξ ,, Λ) A) (I : Ω ⇒ⁱ ψ ⊕ Δ) (J : Θ ⇒ⁱ Ω ⊕ Γ)
              → term-reassoc ([ I ∘ⁱ J ]ⁱ t) ≈ [ extendʳ rename-assoc ]ʳ term-reassoc ([ I ]ⁱ term-reassoc ([ J ]ⁱ t))
  ∘ⁱ-≈-oper (tm-var (var-inl x)) I J = ≈-refl
  ∘ⁱ-≈-oper (tm-var (var-inr x)) I J = ≈-refl
  ∘ⁱ-≈-oper (tm-meta M ts) I J = {!!}
  ∘ⁱ-≈-oper (tm-oper f es) I J = {!!}

  -- proof of the metatheorem obout composition (action of instantiations is functorial)
  ∘ⁱ-≈ (tm-var x) I J = ≈-≡ refl
  ∘ⁱ-≈ (tm-meta M ts) I J = ≈-trans (≈-tm-ˢ {!!}) {!!} -- I don't really know how to begin with this
  ∘ⁱ-≈ (tm-oper f es) I J = ≈-oper λ i → ∘ⁱ-≈-oper (es i) I J

  -- the action of an extension of the identity is the identity
  []ⁱidⁱ-oper : ∀ {Θ Γ Ξ A} (t : Term Θ (Γ ,, Ξ) A)
              → [ extendʳ ctx-empty-left-unit ]ʳ term-reassoc ([ idⁱ ]ⁱ t) ≈ t
  []ⁱidⁱ-oper (tm-var (var-inl x)) = ≈-refl
  []ⁱidⁱ-oper (tm-var (var-inr x)) = ≈-refl
  []ⁱidⁱ-oper (tm-meta M ts) = ≈-meta λ i → ≈-trans (≈-sym (∘r-≈ ([ (λ t → tm-meta t (λ i₁ → [ var-inr ]ʳ tm-var i₁)) ]ⁱ ts i) rename-assoc (extendʳ ctx-empty-left-unit))) {!!}
  []ⁱidⁱ-oper (tm-oper f es) = ≈-oper (λ i → []ⁱidⁱ-oper-aux (es i))
    where
      []ⁱidⁱ-oper-aux : ∀ {Θ Γ Ξ Λ A} (t : Term Θ ((Γ ,, Ξ) ,, Λ) A)
              → [ extendʳ (extendʳ ctx-empty-left-unit) ]ʳ ([ extendʳ rename-assoc ]ʳ term-reassoc ([ idⁱ ]ⁱ t)) ≈ t -- problem with extensions of extensions of functions : should be avoided
      []ⁱidⁱ-oper-aux t = ≈-trans
                          (≈-sym (∘r-≈ ([ rename-assoc ]ʳ ([ idⁱ ]ⁱ t)) (extendʳ rename-assoc) (extendʳ (extendʳ ctx-empty-left-unit))))
                          (≈-trans (≈-sym (∘r-≈ ([ idⁱ ]ⁱ t) rename-assoc ((_ SecondOrder.Renaming.∘ʳ extendʳ (extendʳ ctx-empty-left-unit))
                                                                            (extendʳ rename-assoc)))) {!!})

  -- ** The action of the identity instantiation is the identity **
  []ⁱidⁱ : ∀ {Θ Γ A} (t : Term Θ Γ A)
           → [ ctx-empty-left-unit ]ʳ ([ idⁱ ]ⁱ t) ≈ t
  []ⁱidⁱ (tm-var x) = ≈-refl
  []ⁱidⁱ (tm-meta M ts) = ≈-meta (λ i → []ⁱidⁱ (ts i))
  []ⁱidⁱ (tm-oper f es) = ≈-oper λ i → []ⁱidⁱ-oper (es i)


  -- ** Intantisations preserve syntactical equality of terms **
  ≈-tm-ⁱ : ∀ {Θ Ω Γ Δ A} {s t : Term Θ Δ A} {I : Θ ⇒ⁱ Ω ⊕ Γ}
        → s ≈ t → [ I ]ⁱ s ≈ [ I ]ⁱ t
  ≈-tm-ⁱ (≈-≡ refl) = ≈-refl
  ≈-tm-ⁱ {t = tm-meta M ts} {I = I} (≈-meta ξ) = ≈ˢ[]ˢ {t = I M} (⋈ˢ-≈ˢ-r (λ x → ≈-tm-ⁱ (ξ x)))
  ≈-tm-ⁱ (≈-oper ξ) = ≈-oper λ i → ≈-tm-ʳ (≈-tm-ⁱ (ξ i))
