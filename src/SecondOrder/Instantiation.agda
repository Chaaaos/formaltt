-- {-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.VRenaming
import SecondOrder.MRenaming
import SecondOrder.Term
import SecondOrder.Substitution
import SecondOrder.RelativeMonadMorphism

module SecondOrder.Instantiation
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.VRenaming Σ
  open SecondOrder.MRenaming Σ
  open SecondOrder.Substitution Σ
  open import SecondOrder.RelativeMonadMorphism

  -- metavariable instantiation

  _⇒ⁱ_⊕_ : MContext → MContext → VContext → Set ℓ
  Θ ⇒ⁱ Ξ ⊕ Γ = ∀ {Γᴹ Aᴹ} (M : [ Γᴹ , Aᴹ ]∈ Θ) → Term Ξ (Γ ,, Γᴹ) Aᴹ

  -- syntactic equality of instantiations

  infix 5 _≈ⁱ_

  _≈ⁱ_ : ∀ {Θ Ψ Γ} (I J : Θ ⇒ⁱ Ψ ⊕ Γ) → Set ℓ
  _≈ⁱ_ {Θ} I J = ∀ {Γᴹ Aᴹ} (M : [ Γᴹ , Aᴹ ]∈ Θ) → I M ≈ J M

  -- equality of instantiations is an equivalence relation

  ≈ⁱ-refl : ∀ {Θ Ψ Γ} {I : Θ ⇒ⁱ Ψ ⊕ Γ} → I ≈ⁱ I
  ≈ⁱ-refl M = ≈-refl

  ≈ⁱ-sym : ∀ {Θ Ψ Γ} {I J : Θ ⇒ⁱ Ψ ⊕ Γ} → I ≈ⁱ J → J ≈ⁱ I
  ≈ⁱ-sym ξ M = ≈-sym (ξ M)

  ≈ⁱ-trans : ∀ {Θ Ψ Γ} {I J K : Θ ⇒ⁱ Ψ ⊕ Γ} → I ≈ⁱ J → J ≈ⁱ K → I ≈ⁱ K
  ≈ⁱ-trans ζ ξ M = ≈-trans (ζ M) (ξ M)

  -- extension of an instantiation

  ⇑ⁱ : ∀ {Θ Ψ Γ Δ} → Θ ⇒ⁱ Ψ ⊕ Γ → Θ ⇒ⁱ Ψ ⊕ (Γ ,, Δ)
  ⇑ⁱ I M =  [ ⇑ᵛ var-inl ]ᵛ I M

  -- extension of instantiations preserve equality of instantiations

  ⇑ⁱ-resp-≈ⁱ : ∀ {Θ Ψ Γ Δ} (I J : Θ ⇒ⁱ Ψ ⊕ Γ) → (I ≈ⁱ J) → (⇑ⁱ {Δ = Δ} I ≈ⁱ ⇑ⁱ J)
  ⇑ⁱ-resp-≈ⁱ I J ξ M = []ᵛ-resp-≈ (ξ M)

  -- action of a metavariable instantiation on terms

  infixr 6 [_]ⁱ_

  [_]ⁱ_ : ∀ {Θ ψ Γ} → ψ ⇒ⁱ Θ ⊕ Γ → ∀ {A} → Term ψ Γ A → Term Θ Γ A
  [ I ]ⁱ (tm-var x) = tm-var x
  [ I ]ⁱ (tm-meta M ts) = [ [ idˢ , (λ i → [ I ]ⁱ ts i) ]ˢ ]ˢ (I M)
  [ I ]ⁱ (tm-oper f es) = tm-oper f λ i → [ ⇑ⁱ I ]ⁱ es i

  -- instantiation preserves equality of terms

  []ⁱ-resp-≈ : ∀ {Θ Ξ Γ} (I : Ξ ⇒ⁱ Θ ⊕ Γ) → ∀ {A} {t u : Term Ξ Γ A} →
               t ≈ u → [ I ]ⁱ t ≈ [ I ]ⁱ u
  []ⁱ-resp-≈ I (≈-≡ refl) = ≈-refl
  []ⁱ-resp-≈ I (≈-meta {M = M} ξ) = []ˢ-resp-≈ˢ (I M) ([,]ˢ-resp-≈ˢ (λ x → ≈-refl) λ i → []ⁱ-resp-≈ I (ξ i))
  []ⁱ-resp-≈ I (≈-oper ξ) = ≈-oper λ i → []ⁱ-resp-≈ (⇑ⁱ I) (ξ i)

  -- action preserves equality of instantiation

  []ⁱ-resp-≈ⁱ : ∀ {Θ Ξ Γ} {I J : Ξ ⇒ⁱ Θ ⊕ Γ} → ∀ {A} (t : Term Ξ Γ A) →
               I ≈ⁱ J → [ I ]ⁱ t ≈ [ J ]ⁱ t
  []ⁱ-resp-≈ⁱ (tm-var x) ξ = ≈-refl
  []ⁱ-resp-≈ⁱ (tm-meta M ts) ξ =
    []ˢ-resp-≈ˢ-≈ ([,]ˢ-resp-≈ˢ (λ x → ≈-refl) λ i → []ⁱ-resp-≈ⁱ (ts i) ξ) (ξ M)
  []ⁱ-resp-≈ⁱ {I = I} {J = J} (tm-oper f es) ξ = ≈-oper λ i → []ⁱ-resp-≈ⁱ (es i) (⇑ⁱ-resp-≈ⁱ I J ξ)

  -- generically applied metavariable

  tm-meta-generic : ∀ {Θ} {Γ} {Γᴹ Aᴹ} (M : [ Γᴹ , Aᴹ ]∈ Θ) → Term Θ (Γ ,, Γᴹ) Aᴹ
  tm-meta-generic M = tm-meta M λ i → tm-var (var-inr i)

  -- the action of an instantiation on a generically applied metavariable

  []ⁱ-generic : ∀ {Θ Ξ} {Γ} {I : Θ ⇒ⁱ Ξ ⊕ Γ} {Γᴹ Aᴹ} {M : [ Γᴹ , Aᴹ ]∈ Θ} →
                [ ⇑ⁱ {Δ = Γᴹ} I ]ⁱ tm-meta-generic M ≈ I M
  []ⁱ-generic {Θ = Θ} {Ξ = Ξ} {Γ = Γ} {I = I} {Γᴹ = Γᴹ} {M = M} =
    ≈-trans
      (≈-sym ([ˢ∘ᵛ] (I M)))
      (≈ˢ-idˢ-[]ˢ (λ { (var-inl _) → ≈-refl ; (var-inr _) → ≈-refl}))


  -- Interactions involving instantiations

  -- the identity metavariable instantiation

  idⁱ : ∀ {Θ Γ} → Θ ⇒ⁱ Θ ⊕ Γ
  idⁱ M = tm-meta-generic M

  -- composition of metavariable instantiations

  infixl 6 _∘ⁱ_

  _∘ⁱ_ : ∀ {Θ Ξ Ω Γ} → Ξ ⇒ⁱ Ω ⊕ Γ → Θ ⇒ⁱ Ξ ⊕ Γ → (Θ ⇒ⁱ Ω ⊕ Γ)
  (I ∘ⁱ J) M =  [ ⇑ⁱ I ]ⁱ J M

  -- composition of a renaming and an instantiation

  _ᵛ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → Γ ⇒ᵛ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (ρ ᵛ∘ⁱ I) M = [ ⇑ᵛ ρ ]ᵛ I M

  -- composition of a substitution and an instantiation

  _ˢ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → ψ ⊕ Γ ⇒ˢ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (σ ˢ∘ⁱ I) M = [ ⇑ˢ σ ]ˢ I M

  -- composition of an instantiation and a substitution

  _ⁱ∘ˢ_ : ∀ {Θ ψ Γ Δ} → Θ ⇒ⁱ ψ ⊕ Δ → Θ ⊕ Γ ⇒ˢ Δ →  ψ ⊕ Γ ⇒ˢ Δ
  (I ⁱ∘ˢ σ) x = [ I ]ⁱ σ x

  -- composition of a renaming and an instantiation preerve equality of instantiations

  [ᵛ∘ⁱ]-resp-≈ⁱ : ∀ {Θ ψ Γ Δ} (ρ : Γ ⇒ᵛ Δ) (I J : Θ ⇒ⁱ ψ ⊕ Γ) → (I ≈ⁱ J) → (ρ ᵛ∘ⁱ I) ≈ⁱ (ρ ᵛ∘ⁱ J)
  [ᵛ∘ⁱ]-resp-≈ⁱ σ I J ξ M = []ᵛ-resp-≈ (ξ M)

  -- composition of a renaming and an instantiation preserve equality of instantiations

  [ˢ∘ⁱ]-resp-≈ⁱ : ∀ {Θ ψ Γ Δ} (σ : ψ ⊕ Γ ⇒ˢ Δ) (I J : Θ ⇒ⁱ ψ ⊕ Γ) → (I ≈ⁱ J) → (σ ˢ∘ⁱ I) ≈ⁱ (σ ˢ∘ⁱ J)
  [ˢ∘ⁱ]-resp-≈ⁱ σ I J ξ M = []ˢ-resp-≈ (⇑ˢ σ) (ξ M)


  -- Actions correspondig to the interactions

  -- the action of the identity

  [idⁱ] : ∀ {Θ Γ A Δ} {t : Term Θ (Γ ,, Δ) A}  → [ idⁱ ]ⁱ t ≈ t
  [idⁱ] {t = tm-var x} = ≈-refl
  [idⁱ] {t = tm-meta M ts} = ≈-meta (λ i → [idⁱ])
  [idⁱ] {t = tm-oper f es} = ≈-oper (λ i → [idⁱ])

  -- extension commutes with composition of renaming and substitution

  ⇑ⁱ-resp-ᵛ∘ⁱ : ∀ {Θ ψ} {Γ Δ Ξ} {I : Θ ⇒ⁱ ψ ⊕ Γ} {ρ : Γ ⇒ᵛ Δ}
               → ⇑ⁱ {Δ = Ξ} (ρ ᵛ∘ⁱ I) ≈ⁱ ⇑ᵛ ρ ᵛ∘ⁱ ⇑ⁱ I
  ⇑ⁱ-resp-ᵛ∘ⁱ {ρ = ρ} M = ≈-trans (≈-sym [∘ᵛ]) (≈-trans ([]ᵛ-resp-≡ᵛ λ {(var-inl _) → refl ; (var-inr x) → refl}) [∘ᵛ])

  -- the action of the composition of an instantiation and a renaming

  [ᵛ∘ⁱ] : ∀ {Θ Ψ Γ Δ A} {ρ : Γ ⇒ᵛ Δ} {I : Θ ⇒ⁱ Ψ ⊕ Γ} (t : Term Θ Γ A) →
           [ ρ ]ᵛ [ I ]ⁱ t ≈ [ ρ ᵛ∘ⁱ I ]ⁱ [ ρ ]ᵛ t
  [ᵛ∘ⁱ] (tm-var x) = ≈-refl
  [ᵛ∘ⁱ] {I = I} (tm-meta M ts) =
    ≈-trans
     (≈-sym ([ᵛ∘ˢ] (I M)))
     (≈-trans
       ([]ˢ-resp-≈ˢ (I M) (λ { (var-inl _) → ≈-refl ; (var-inr j) → [ᵛ∘ⁱ] (ts j)}))
       ([ˢ∘ᵛ] (I M)))
  [ᵛ∘ⁱ] {ρ = ρ} {I = I} (tm-oper f es) =
    ≈-oper λ i → ≈-trans ([ᵛ∘ⁱ] (es i)) ([]ⁱ-resp-≈ⁱ ([ ⇑ᵛ ρ ]ᵛ es i) (≈ⁱ-sym (⇑ⁱ-resp-ᵛ∘ⁱ {I = I})))


  -- extension commutes with composition

  ⇑ⁱ-resp-∘ⁱ : ∀ {Θ Ξ Ω} {Γ Δ} {I : Θ ⇒ⁱ Ξ ⊕ Γ} {J : Ξ ⇒ⁱ Ω ⊕ Γ} →
               ⇑ⁱ {Δ = Δ} (J ∘ⁱ I) ≈ⁱ ⇑ⁱ J ∘ⁱ ⇑ⁱ I
  ⇑ⁱ-resp-∘ⁱ {I = I} {J = J} M =
    ≈-trans
     ([ᵛ∘ⁱ] (I M))
     ([]ⁱ-resp-≈ⁱ
        ([ ⇑ᵛ var-inl ]ᵛ I M)
        (λ N → ≈-trans
                 (≈-sym [∘ᵛ])
                 (≈-trans
                   ([]ᵛ-resp-≡ᵛ (λ { (var-inl x) → refl ; (var-inr x) → refl }))
                   [∘ᵛ])))


  ⇑ˢ-resp-ⁱ∘ˢ : ∀ {Θ ψ Γ Δ Ξ} → {I : Θ ⇒ⁱ ψ ⊕ Δ} → {σ : Θ ⊕ Γ ⇒ˢ Δ}
    → ⇑ˢ {Ξ = Ξ} (I ⁱ∘ˢ σ) ≈ˢ ⇑ⁱ I ⁱ∘ˢ ⇑ˢ σ
  ⇑ˢ-resp-ⁱ∘ˢ {σ = σ} (var-inl x) = [ᵛ∘ⁱ] (σ x)
  ⇑ˢ-resp-ⁱ∘ˢ (var-inr x) = ≈-refl

  [ˢ∘ⁱ] : ∀ {Θ Ψ Γ Γ' Δ A} {σ : Ψ ⊕ Γ ⇒ˢ Γ'} {I : Θ ⇒ⁱ Ψ ⊕ Γ} (t : Term Θ Γ' A)
        → [ σ ˢ∘ⁱ I ]ⁱ t ≈ {! [ I ]ⁱ t!}
  [ˢ∘ⁱ] t = {!!}



  ⇑ⁱ-resp-ˢ∘ⁱ : ∀ {Θ Ψ Γ Γ' Δ} {I : Θ ⇒ⁱ Ψ ⊕ Γ} {f : Ψ ⊕ Γ ⇒ˢ Γ'}
       → ⇑ⁱ {Θ} {Ψ} {Γ'} {Δ} (f ˢ∘ⁱ I) ≈ⁱ (⇑ˢ f) ˢ∘ⁱ (⇑ⁱ I)
  ⇑ⁱ-resp-ˢ∘ⁱ var-slot = {!!}
  ⇑ⁱ-resp-ˢ∘ⁱ (var-inl M) = {!!}
  ⇑ⁱ-resp-ˢ∘ⁱ (var-inr N) = {!!}

  -- interaction lemma
  []ⁱ-[]ˢ : ∀ {Θ Ψ Γ Δ A} {I : Θ ⇒ⁱ Ψ ⊕ Δ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {ρ : Δ ⇒ᵛ Γ} (t : Term Θ Γ A) →
        σ ˢ∘ᵛ ρ ≈ˢ idˢ → ([ I ]ⁱ ([ σ ]ˢ t)) ≈ ([ I ⁱ∘ˢ σ ]ˢ [ ρ ᵛ∘ⁱ I ]ⁱ t)
  []ⁱ-[]ˢ (tm-var x) ξ = ≈-refl
  []ⁱ-[]ˢ {I = I} {σ = σ} {ρ = ρ} (tm-meta M ts) ξ =
   ≈-trans
     ([]ˢ-resp-≈ˢ (I M)
        (λ { (var-inl i) → []ⁱ-resp-≈ I (≈-sym (ξ i)) ; (var-inr j) → []ⁱ-[]ˢ (ts j) ξ}))
     (≈-trans
       ([ˢ∘ᵛ] (I M))
       ([∘ˢ] ((ρ ᵛ∘ⁱ I) M)))
  []ⁱ-[]ˢ {I = I} {σ = σ} {ρ = ρ} (tm-oper f es) ξ =
    ≈-oper λ i →
      ≈-trans
       ([]ⁱ-[]ˢ {σ = ⇑ˢ σ} {ρ = ⇑ᵛ ρ} (es i)
         (≈ˢ-trans
           (≈ˢ-sym (⇑ˢ-resp-ˢ∘ᵛ  {ρ = ρ} {σ = σ}))
           (≈ˢ-trans (⇑ˢ-resp-≈ˢ ξ) ⇑ˢ-resp-idˢ)))
       ([]ˢ-resp-≈ˢ-≈
          {σ = ⇑ⁱ I ⁱ∘ˢ ⇑ˢ σ }
          {τ = ⇑ˢ (I ⁱ∘ˢ σ)}
          {t = ([ ⇑ᵛ ρ ᵛ∘ⁱ ⇑ⁱ I ]ⁱ es i)}
          {u = ([ ⇑ⁱ (ρ ᵛ∘ⁱ I) ]ⁱ es i)}
          (≈ˢ-sym ⇑ˢ-resp-ⁱ∘ˢ)
          ([]ⁱ-resp-≈ⁱ (es i) (≈ⁱ-sym (⇑ⁱ-resp-ᵛ∘ⁱ {I = I}))))

  -- the action of a composition is functorial

  [∘ⁱ] : ∀ {Θ Ξ Ω Γ} → {I : Θ ⇒ⁱ Ξ ⊕ Γ} → {J : Ξ ⇒ⁱ Ω ⊕ Γ} →
           ∀ {A} → ∀ (t : Term Θ Γ A) → [ J ∘ⁱ I ]ⁱ t ≈ [ J ]ⁱ [ I ]ⁱ t
  [∘ⁱ] (tm-var x) = ≈-refl
  [∘ⁱ] {Θ = Θ} {Ξ = Ξ} {Γ = Γ} {I = I} {J = J} (tm-meta {Γᴹ = Γᴹ} M ts) =
    ≈-trans
      ([]ˢ-resp-≈ˢ
        ([ ⇑ⁱ J ]ⁱ (I M))
        ([,]ˢ-resp-≈ˢ (λ x → ≈-refl) (λ i → [∘ⁱ] {I = I} {J = J} (ts i))))
      (≈-trans
        ([]ˢ-resp-≈ˢ {τ = λ i → [ J ]ⁱ var-or-ts i} ([ ⇑ⁱ J ]ⁱ (I M))
        λ {(var-inl x) → ≈-refl ; (var-inr y) → ≈-refl})
        (≈-trans
           (≈-sym ([]ⁱ-[]ˢ {I = J} {σ = var-or-ts} {ρ = var-inl} (I M) λ x → ≈-refl))
            ([]ⁱ-resp-≈ J
                       ([]ˢ-resp-≈ˢ (I M) λ { (var-inl x) → ≈-refl ; (var-inr x) → ≈-refl}))))
                 where
                 var-or-ts : ∀ {A} → A ∈ (Γ ,, Γᴹ) → Term Ξ Γ A
                 var-or-ts (var-inl x) = tm-var x
                 var-or-ts (var-inr y) = [ I ]ⁱ ts y

  [∘ⁱ] {I = I} {J = J} (tm-oper f es) =
            ≈-oper (λ i → ≈-trans ([]ⁱ-resp-≈ⁱ (es i) (⇑ⁱ-resp-∘ⁱ {I = I})) ([∘ⁱ] (es i)))


-- The category of metacontext and instantiations

  module _ {Γ} where

    open import Categories.Category

    Metacontexts-Insts : Category ℓ ℓ ℓ
    Metacontexts-Insts =
      record
        { Obj = MContext --VContext
        ; _⇒_ = _⇒ⁱ_⊕ Γ
        ; _≈_ =  _≈ⁱ_
        ; id = idⁱ
        ; _∘_ = _∘ⁱ_
        ; assoc = λ {Θ} {Ω} {ψ} {Ξ} {K} {J} {I} {Γᴹ} {Aᴹ} M →
                                                            ≈-trans
                                                              ([]ⁱ-resp-≈ⁱ (K M) (⇑ⁱ-resp-∘ⁱ {Δ = Γᴹ} {I = J} {J = I}))
                                                              ([∘ⁱ] (K M))
        ; sym-assoc =  λ {Θ} {Ω} {ψ} {Ξ} {K} {J} {I} {Γᴹ} {Aᴹ} M → ≈-sym
                                                               ( ≈-trans
                                                              ([]ⁱ-resp-≈ⁱ (K M) (⇑ⁱ-resp-∘ⁱ {Δ = Γᴹ} {I = J} {J = I}))
                                                              ([∘ⁱ] (K M)))
        ; identityˡ = λ M → [idⁱ]
        ; identityʳ = λ {A} {B} {I} M →
                                    ≈-trans
                                      (≈-trans
                                        (≈-sym ([ˢ∘ᵛ] (I M)))
                                        ([]ˢ-resp-≈ˢ (I M) λ x → {!!}))
                                      [idˢ] -- λ x → faire une disjonction de cas ailleurs plus tard : flemme là tout de suite
        ; identity² = λ M → ≈-refl
        ; equiv =  record
                     { refl = λ {I} → ≈ⁱ-refl {I = I}
                     ; sym = ≈ⁱ-sym
                     ; trans = ≈ⁱ-trans }
        ; ∘-resp-≈ = {!!} -- λ f≈ˢg g≈ˢi x → []ˢ-resp-≈ˢ-≈ f≈ˢg (g≈ˢi x)
        }

        where
          idʳ : ∀ {Θ Δ A} (x : A ∈ (Γ ,, Δ)) →
                                        [ tm-var , (λ i → tm-var (var-inr i)) ]ˢ
                                        ([ (λ x₁ → var-inl {Γ = Γ ,, Δ} (var-inl x₁)) , (λ x₁ → var-inr x₁) ]ᵛ x)
                                        ≈ tm-var {Θ = Θ} x
          idʳ (var-inl x) = {!!}
          idʳ (var-inr x) = {!!}
