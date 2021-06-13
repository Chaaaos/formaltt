open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.VRenaming
import SecondOrder.MRenaming
import SecondOrder.Term
import SecondOrder.Substitution
import SecondOrder.RMonadsMorphism

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
  open import SecondOrder.RMonadsMorphism

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
  ⇑ⁱ I M =  [ ⇑ᵛʳ var-inl ]ᵛʳ I M

  -- extension of instantiations preserve equality of instantiations

  ⇑ⁱ-resp-≈ⁱ : ∀ {Θ Ψ Γ Δ} (I J : Θ ⇒ⁱ Ψ ⊕ Γ) → (I ≈ⁱ J) → (⇑ⁱ {Δ = Δ} I ≈ⁱ ⇑ⁱ J)
  ⇑ⁱ-resp-≈ⁱ I J ξ M = []ᵛʳ-resp-≈ (ξ M)

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
      (≈-sym ([ˢ∘ᵛʳ]ˢ (I M)))
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

  _ᵛʳ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → Γ ⇒ᵛʳ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (ρ ᵛʳ∘ⁱ I) M = [ ⇑ᵛʳ ρ ]ᵛʳ I M

  -- composition of a substitution and an instantiation

  _ˢ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → ψ ⊕ Γ ⇒ˢ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (σ ˢ∘ⁱ I) M = [ ⇑ˢ σ ]ˢ I M

  -- composition of an instantiation and a substitution

  _ⁱ∘ˢ_ : ∀ {Θ ψ Γ Δ} → Θ ⇒ⁱ ψ ⊕ Δ → Θ ⊕ Γ ⇒ˢ Δ →  ψ ⊕ Γ ⇒ˢ Δ
  (I ⁱ∘ˢ σ) x = [ I ]ⁱ σ x

  -- composition of a renaming and an instantiation preerve equality of instantiations

  [ᵛʳ∘ⁱ]ⁱ-resp-≈ⁱ : ∀ {Θ ψ Γ Δ} (ρ : Γ ⇒ᵛʳ Δ) (I J : Θ ⇒ⁱ ψ ⊕ Γ) → (I ≈ⁱ J) → (ρ ᵛʳ∘ⁱ I) ≈ⁱ (ρ ᵛʳ∘ⁱ J)
  [ᵛʳ∘ⁱ]ⁱ-resp-≈ⁱ σ I J ξ M = []ᵛʳ-resp-≈ (ξ M)

  -- composition of a renaming and an instantiation preserve equality of instantiations

  [ˢ∘ⁱ]ⁱ-resp-≈ⁱ : ∀ {Θ ψ Γ Δ} (σ : ψ ⊕ Γ ⇒ˢ Δ) (I J : Θ ⇒ⁱ ψ ⊕ Γ) → (I ≈ⁱ J) → (σ ˢ∘ⁱ I) ≈ⁱ (σ ˢ∘ⁱ J)
  [ˢ∘ⁱ]ⁱ-resp-≈ⁱ σ I J ξ M = []ˢ-resp-≈ (⇑ˢ σ) (ξ M)


  -- Actions correspondig to the interactions

  -- the action of the identity

  [id]ⁱ : ∀ {Θ Γ A Δ} {t : Term Θ (Γ ,, Δ) A}  → [ idⁱ ]ⁱ t ≈ t
  [id]ⁱ {t = tm-var x} = ≈-refl
  [id]ⁱ {t = tm-meta M ts} = ≈-meta (λ i → [id]ⁱ)
  [id]ⁱ {t = tm-oper f es} = ≈-oper (λ i → [id]ⁱ)

  -- extension commutes with composition of renaming and substitution

  ⇑ⁱ-resp-ᵛʳ∘ⁱ : ∀ {Θ ψ} {Γ Δ Ξ} {I : Θ ⇒ⁱ ψ ⊕ Γ} {ρ : Γ ⇒ᵛʳ Δ}
               → ⇑ⁱ {Δ = Ξ} (ρ ᵛʳ∘ⁱ I) ≈ⁱ ⇑ᵛʳ ρ ᵛʳ∘ⁱ ⇑ⁱ I
  ⇑ⁱ-resp-ᵛʳ∘ⁱ {ρ = ρ} M = ≈-trans (≈-sym [∘]ᵛʳ) (≈-trans ([]ᵛʳ-resp-≡ᵛʳ λ {(var-inl _) → refl ; (var-inr x) → refl}) [∘]ᵛʳ)

  -- the action of the composition of an instantiation and a renaming

  [ᵛʳ∘ⁱ]ⁱ : ∀ {Θ Ψ Γ Δ A} {ρ : Γ ⇒ᵛʳ Δ} {I : Θ ⇒ⁱ Ψ ⊕ Γ} (t : Term Θ Γ A) →
           [ ρ ]ᵛʳ [ I ]ⁱ t ≈ [ ρ ᵛʳ∘ⁱ I ]ⁱ [ ρ ]ᵛʳ t
  [ᵛʳ∘ⁱ]ⁱ (tm-var x) = ≈-refl
  [ᵛʳ∘ⁱ]ⁱ {I = I} (tm-meta M ts) =
    ≈-trans
     (≈-sym ([ᵛʳ∘ˢ]ˢ (I M)))
     (≈-trans
       ([]ˢ-resp-≈ˢ (I M) (λ { (var-inl _) → ≈-refl ; (var-inr j) → [ᵛʳ∘ⁱ]ⁱ (ts j)}))
       ([ˢ∘ᵛʳ]ˢ (I M)))
  [ᵛʳ∘ⁱ]ⁱ {ρ = ρ} {I = I} (tm-oper f es) =
    ≈-oper λ i → ≈-trans ([ᵛʳ∘ⁱ]ⁱ (es i)) ([]ⁱ-resp-≈ⁱ ([ ⇑ᵛʳ ρ ]ᵛʳ es i) (≈ⁱ-sym (⇑ⁱ-resp-ᵛʳ∘ⁱ {I = I})))

  -- extension commutes with composition

  ⇑ⁱ-resp-∘ⁱ : ∀ {Θ Ξ Ω} {Γ Δ} {I : Θ ⇒ⁱ Ξ ⊕ Γ} {J : Ξ ⇒ⁱ Ω ⊕ Γ} →
               ⇑ⁱ {Δ = Δ} (J ∘ⁱ I) ≈ⁱ ⇑ⁱ J ∘ⁱ ⇑ⁱ I
  ⇑ⁱ-resp-∘ⁱ {I = I} {J = J} M =
    ≈-trans
     ([ᵛʳ∘ⁱ]ⁱ (I M))
     ([]ⁱ-resp-≈ⁱ
        ([ ⇑ᵛʳ var-inl ]ᵛʳ I M)
        (λ N → ≈-trans
                 (≈-sym [∘]ᵛʳ)
                 (≈-trans
                   ([]ᵛʳ-resp-≡ᵛʳ (λ { (var-inl x) → refl ; (var-inr x) → refl }))
                   [∘]ᵛʳ)))

  ⇑ˢ-resp-ⁱ∘ˢ : ∀ {Θ ψ Γ Δ Ξ} → {I : Θ ⇒ⁱ ψ ⊕ Δ} → {σ : Θ ⊕ Γ ⇒ˢ Δ} → ⇑ˢ {Ξ = Ξ} (I ⁱ∘ˢ σ) ≈ˢ ⇑ⁱ I ⁱ∘ˢ ⇑ˢ σ
  ⇑ˢ-resp-ⁱ∘ˢ {σ = σ} (var-inl x) = [ᵛʳ∘ⁱ]ⁱ (σ x)
  ⇑ˢ-resp-ⁱ∘ˢ (var-inr x) = ≈-refl

  -- interaction lemma
  []ⁱ-[]ˢ : ∀ {Θ Ψ Γ Δ A} {I : Θ ⇒ⁱ Ψ ⊕ Δ} {σ : Θ ⊕ Γ ⇒ˢ Δ} {ρ : Δ ⇒ᵛʳ Γ} (t : Term Θ Γ A) →
        σ ˢ∘ᵛʳ ρ ≈ˢ idˢ → ([ I ]ⁱ ([ σ ]ˢ t)) ≈ ([ I ⁱ∘ˢ σ ]ˢ [ ρ ᵛʳ∘ⁱ I ]ⁱ t)
  []ⁱ-[]ˢ (tm-var x) ξ = ≈-refl
  []ⁱ-[]ˢ {I = I} {σ = σ} {ρ = ρ} (tm-meta M ts) ξ =
   ≈-trans
     ([]ˢ-resp-≈ˢ (I M)
        (λ { (var-inl i) → []ⁱ-resp-≈ I (≈-sym (ξ i)) ; (var-inr j) → []ⁱ-[]ˢ (ts j) ξ}))
     (≈-trans
       ([ˢ∘ᵛʳ]ˢ (I M))
       ([∘]ˢ ((ρ ᵛʳ∘ⁱ I) M)))
  []ⁱ-[]ˢ {I = I} {σ = σ} {ρ = ρ} (tm-oper f es) ξ =
    ≈-oper λ i →
      ≈-trans
       ([]ⁱ-[]ˢ {σ = ⇑ˢ σ} {ρ = ⇑ᵛʳ ρ} (es i)
         (≈ˢ-trans
           (≈ˢ-sym (⇑ˢ-ˢ∘ᵛʳ  {ρ = ρ} {σ = σ}))
           (≈ˢ-trans (⇑ˢ-resp-≈ˢ ξ) ⇑ˢ-idˢ)))
       ([]ˢ-resp-≈ˢ-≈
          {σ = ⇑ⁱ I ⁱ∘ˢ ⇑ˢ σ }
          {τ = ⇑ˢ (I ⁱ∘ˢ σ)}
          {t = ([ ⇑ᵛʳ ρ ᵛʳ∘ⁱ ⇑ⁱ I ]ⁱ es i)}
          {u = ([ ⇑ⁱ (ρ ᵛʳ∘ⁱ I) ]ⁱ es i)}
          (≈ˢ-sym ⇑ˢ-resp-ⁱ∘ˢ)
          ([]ⁱ-resp-≈ⁱ (es i) (≈ⁱ-sym (⇑ⁱ-resp-ᵛʳ∘ⁱ {I = I}))))

  -- the action of a composition

  [∘]ⁱ : ∀ {Θ Ξ Ω Γ} → {I : Θ ⇒ⁱ Ξ ⊕ Γ} → {J : Ξ ⇒ⁱ Ω ⊕ Γ} →
           ∀ {A} → ∀ (t : Term Θ Γ A) → [ J ∘ⁱ I ]ⁱ t ≈ [ J ]ⁱ [ I ]ⁱ t
  [∘]ⁱ (tm-var x) = ≈-refl
  [∘]ⁱ {Θ = Θ} {Ξ = Ξ} {Γ = Γ} {I = I} {J = J} (tm-meta {Γᴹ = Γᴹ} M ts) =
    ≈-trans
      ([]ˢ-resp-≈ˢ
        ([ ⇑ⁱ J ]ⁱ (I M))
        ([,]ˢ-resp-≈ˢ (λ x → ≈-refl) (λ i → [∘]ⁱ {I = I} {J = J} (ts i))))
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

  [∘]ⁱ {I = I} {J = J} (tm-oper f es) =
            ≈-oper (λ i → ≈-trans ([]ⁱ-resp-≈ⁱ (es i) (⇑ⁱ-resp-∘ⁱ {I = I})) ([∘]ⁱ (es i)))
