open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Renaming
import SecondOrder.Term
import SecondOrder.Substitution

module SecondOrder.Instantiation
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.Renaming Σ
  open SecondOrder.Substitution Σ

  -- metavariable instantiation

  _⇒ⁱ_⊕_ : MetaContext → MetaContext → Context → Set ℓ
  Θ ⇒ⁱ Ξ ⊕ Γ = ∀ (M : mv Θ) → Term Ξ (Γ ,, mv-arity Θ M) (mv-sort Θ M)

  -- the identity metavariable instantiation

  idⁱ : ∀ {Θ} → Θ ⇒ⁱ Θ ⊕ ctx-empty
  idⁱ t = tm-meta t (λ i → [ var-inr ]ʳ (tm-var i))

  -- action of a metavariable instantiation on terms

  infixr 6 [_]ⁱ_

  [_]ⁱ_ : ∀ {Θ Ξ Γ Δ A} → Ξ ⇒ⁱ Θ ⊕ Δ → Term Ξ Γ A → Term Θ (Δ ,, Γ) A
  [ I ]ⁱ (tm-var x) = tm-var (var-inr x)
  [ I ]ⁱ (tm-meta M ts) =  [ [ inlˢ , (λ i → [ I ]ⁱ (ts i)) ]ˢ ]ˢ I M
  [ I ]ⁱ (tm-oper f es) = tm-oper f λ i →  [ assoc-r ]ˢ [ I ]ⁱ es i

  -- composition of metavariable instantiations

  infixl 5 _∘ⁱ_

  _∘ⁱ_ : ∀ {Θ Ξ Ω Γ Δ} → Ξ ⇒ⁱ Ω ⊕ Δ → Θ ⇒ⁱ Ξ ⊕ Γ → (Θ ⇒ⁱ Ω ⊕ (Δ ,, Γ))
  (I ∘ⁱ J) M =  [ assoc-r ]ˢ [ I ]ⁱ (J M)

  -- syntactic equality of instantiations
  _≈ⁱ_ : ∀ {Θ Ξ Γ} (I J : Θ ⇒ⁱ Ξ ⊕ Γ) → Set ℓ
  _≈ⁱ_ {Θ} I J = ∀ (M : mv Θ) → I M ≈ J M

  -- as a special case we define instantiation of a closed term such that
  -- the empty context does not appear. This is used when axioms are instantiated.
  instantiate-closed-term : ∀ {Θ Ξ Γ A} (I : Θ ⇒ⁱ Ξ ⊕ Γ) → Term Θ ctx-empty A → Term Ξ Γ A
  instantiate-closed-term I t =  [ sum-ctx-empty-r ]ˢ ([ I ]ⁱ t)


  --------------------------------------------------------------------------------------------------
  ----------------------------------------------------------------------
  --          Interactions with renamings and substitutions           --
  ----------------------------------------------------------------------

  -- action of a renaming on an instantiation
  _ʳ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → Γ ⇒ʳ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (ρ ʳ∘ⁱ I) M = [ (⇑ʳ ρ) ]ʳ I M

  -- action of a substitution on an instantiation
  _ˢ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → ψ ⊕ Γ ⇒ˢ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (σ ˢ∘ⁱ I) M = [ ⇑ˢ σ ]ˢ I M

  -- action of an instantiation on a substitution
  _ⁱ∘ˢ_ : ∀ {Θ ψ Γ Δ Ξ} → Θ ⇒ⁱ ψ ⊕ Ξ → Θ ⊕ Γ ⇒ˢ Δ →  ψ ⊕ (Ξ ,, Γ) ⇒ˢ (Ξ ,, Δ)
  (I ⁱ∘ˢ σ) (var-inl x) = tm-var (var-inl x)
  (I ⁱ∘ˢ σ) (var-inr x) = [ I ]ⁱ (σ x)


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
                                               ([]ˢ-resp-≈ˢ
                                                 {σ = [ inlˢ , (λ x → [ I ]ⁱ ts x) ]ˢ}
                                                 {τ =  [ inlˢ , (λ x → [ J ]ⁱ ts x) ]ˢ }
                                                 (I M)
                                                 (uniqueˢ { τ = [ inlˢ , (λ x → [ J ]ⁱ ts x) ]ˢ} (λ x → ≈-refl) λ x → ≈-sym (≈ⁱ[]ⁱ {t = ts x} p)))
                                                 ([]ˢ-resp-≈ [ var-inl ʳ∘ˢ tm-var , (λ x → [ J ]ⁱ ts x) ]ˢ (p M))
  ≈ⁱ[]ⁱ {t = tm-oper f es} p = ≈-oper λ i → []ˢ-resp-≈ assoc-r (≈ⁱ[]ⁱ {t = es i} p)

  -- interaction


  -- ** Action of instantiation is functirial wrt. composition ** (the proof comes later)
  ∘ⁱ-≈ : ∀ {Θ Ω ψ Γ Δ Ξ A} (t : Term Θ Ξ A) (I : Ω ⇒ⁱ ψ ⊕ Δ) (J : Θ ⇒ⁱ Ω ⊕ Γ)
        → [ I ∘ⁱ J ]ⁱ t ≈ [ assoc-r ]ˢ ([ I ]ⁱ ([ J ]ⁱ t))

  -- reassociation of a composition
  reassoc-∘ⁱ : ∀ {Θ Ω ψ Γ Δ Ξ Λ A} (t : Term Θ (Ξ ,, Λ) A) (I : Ω ⇒ⁱ ψ ⊕ Δ) (J : Θ ⇒ⁱ Ω ⊕ Γ)
              → [ assoc-r ]ˢ ([ I ∘ⁱ J ]ⁱ t) ≈  [ assoc-r ]ˢ ([ assoc-r ]ˢ ([ I ]ⁱ ([ J ]ⁱ t)))
  reassoc-∘ⁱ t I J = []ˢ-resp-≈ assoc-r (∘ⁱ-≈ t I J)

  -- auxiliary function, to deal with extensions in the oper case
  ∘ⁱ-≈-oper : ∀ {Θ Ω ψ Γ Δ Ξ Λ A} (t : Term Θ (Ξ ,, Λ) A) (I : Ω ⇒ⁱ ψ ⊕ Δ) (J : Θ ⇒ⁱ Ω ⊕ Γ)
              → [ assoc-r ]ˢ ([ I ∘ⁱ J ]ⁱ t) ≈ [ ⇑ˢ assoc-r ]ˢ [ assoc-r ]ˢ ([ I ]ⁱ [ assoc-r ]ˢ ([ J ]ⁱ t))
  ∘ⁱ-≈-oper (tm-var (var-inl x)) I J = ≈-refl
  ∘ⁱ-≈-oper (tm-var (var-inr x)) I J = ≈-refl
  ∘ⁱ-≈-oper (tm-meta M ts) I J = {!!}
  ∘ⁱ-≈-oper (tm-oper f es) I J = {!!}

  -- proof of the metatheorem obout composition (action of instantiations is functorial)
  ∘ⁱ-≈ (tm-var x) I J = ≈-≡ refl
  ∘ⁱ-≈ (tm-meta M ts) I J = ≈-sym ( ≈-trans ([]ˢ-resp-≈ assoc-r {!!}) {!!} )-- I don't really know how to begin with this
  ∘ⁱ-≈ (tm-oper f es) I J = ≈-oper λ i → ∘ⁱ-≈-oper (es i) I J

-- [ I ∘ⁱ J ]ⁱ tm-meta M ts ≈
--    [ assoc-r ]ˢ [ I ]ⁱ [ J ]ⁱ tm-meta M ts

  -- the action of an extension of the identity is the identity
  []ⁱidⁱ-oper : ∀ {Θ Γ Ξ A} (t : Term Θ (Γ ,, Ξ) A)
              → [ ⇑ˢ sum-ctx-empty-l ]ˢ [ assoc-r ]ˢ ([ idⁱ ]ⁱ t) ≈ t
  []ⁱidⁱ-oper (tm-var (var-inl x)) = ≈-refl
  []ⁱidⁱ-oper (tm-var (var-inr x)) = ≈-refl
  []ⁱidⁱ-oper (tm-meta M ts) = ≈-meta λ i → ≈-trans (≈-sym ([∘]ˢ {σ = assoc-r} {τ = (⇑ˢ sum-ctx-empty-l)} ([ (λ t → tm-meta t (λ i₁ → [ var-inr ]ʳ tm-var i₁)) ]ⁱ ts i))) {!!}
  []ⁱidⁱ-oper (tm-oper f es) = ≈-oper (λ i → []ⁱidⁱ-oper-aux (es i))
    where
      []ⁱidⁱ-oper-aux : ∀ {Θ Γ Ξ Λ A} (t : Term Θ ((Γ ,, Ξ) ,, Λ) A)
              → [ ⇑ˢ (⇑ˢ sum-ctx-empty-l) ]ˢ ([ ⇑ˢ assoc-r ]ˢ ([ assoc-r ]ˢ ([ idⁱ ]ⁱ t))) ≈ t -- problem with extensions of extensions of functions : should be avoided
      []ⁱidⁱ-oper-aux t = ≈-trans
                          (≈-sym ([∘]ˢ  {σ = ⇑ˢ assoc-r} {τ = (⇑ˢ (⇑ˢ sum-ctx-empty-l))} ([ assoc-r ]ˢ ([ idⁱ ]ⁱ t))))
                          (≈-trans (≈-sym ([∘]ˢ  {σ = assoc-r} {τ = ⇑ˢ (⇑ˢ sum-ctx-empty-l) ∘ˢ ⇑ˢ assoc-r} ([ idⁱ ]ⁱ t)))
                                                                           {!!} )


  -- ** The action of the identity instantiation is the identity **
  []ⁱidⁱ : ∀ {Θ Γ A} (t : Term Θ Γ A)
           → [ sum-ctx-empty-l ]ˢ ([ idⁱ ]ⁱ t) ≈ t
  []ⁱidⁱ (tm-var x) = ≈-refl
  []ⁱidⁱ (tm-meta M ts) = ≈-meta (λ i → []ⁱidⁱ (ts i))
  []ⁱidⁱ (tm-oper f es) = ≈-oper λ i → []ⁱidⁱ-oper (es i)


  -- ** Intantisations preserve syntactical equality of terms **
  ≈-tm-ⁱ : ∀ {Θ Ω Γ Δ A} {s t : Term Θ Δ A} {I : Θ ⇒ⁱ Ω ⊕ Γ}
        → s ≈ t → [ I ]ⁱ s ≈ [ I ]ⁱ t
  ≈-tm-ⁱ (≈-≡ refl) = ≈-refl
  ≈-tm-ⁱ {t = tm-meta M ts} {I = I} (≈-meta ξ) = []ˢ-resp-≈ˢ (I M) (uniqueˢ {τ = [ inlˢ , (λ i → [ I ]ⁱ ts i) ]ˢ} (λ x → ≈-refl) λ x → ≈-sym (≈-tm-ⁱ (ξ x)))
  ≈-tm-ⁱ (≈-oper ξ) = ≈-oper λ i → []ˢ-resp-≈ assoc-r (≈-tm-ⁱ (ξ i))
