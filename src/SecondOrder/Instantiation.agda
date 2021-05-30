{-# OPTIONS --allow-unsolved-metas #-}

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

  _≈ⁱ_ : ∀ {Θ Ξ Γ} (I J : Θ ⇒ⁱ Ξ ⊕ Γ) → Set ℓ
  _≈ⁱ_ {Θ} I J = ∀ {Γᴹ Aᴹ} (M : [ Γᴹ , Aᴹ ]∈ Θ) → I M ≈ J M

  -- extension of an instantiation

  ⇑ⁱ : ∀ {Θ Ξ Γ Δ} → Θ ⇒ⁱ Ξ ⊕ Γ → Θ ⇒ⁱ Ξ ⊕ (Γ ,, Δ)
  ⇑ⁱ I M =  [ ⇑ʳ var-inl ]ʳ I M

  -- extension of instantiations preserve equality of instantiations

  ⇑ⁱ-resp-≈ⁱ : ∀ {Θ Ξ Γ Δ} (I J : Θ ⇒ⁱ Ξ ⊕ Γ) → (I ≈ⁱ J) → (⇑ⁱ {Δ = Δ} I ≈ⁱ ⇑ⁱ J)
  ⇑ⁱ-resp-≈ⁱ I J ξ M = []ʳ-resp-≈ (ξ M)

  -- action of a metavariable instantiation on terms

  infixr 6 [_]ⁱ_

  [_]ⁱ_ : ∀ {Θ ψ Γ} → ψ ⇒ⁱ Θ ⊕ Γ → ∀ {A} → Term ψ Γ A → Term Θ Γ A
  [ I ]ⁱ (tm-var x) = tm-var x
  [ I ]ⁱ (tm-meta M ts) = [ [ idˢ , (λ i → [ I ]ⁱ ts i) ]ˢ ]ˢ (I M)
  [ I ]ⁱ (tm-oper f es) = tm-oper f λ i → [ ⇑ⁱ I ]ⁱ es i

  -- instantiation preserves equality of terms

  []ⁱ-resp-≈ : ∀ {Θ Ξ Γ} (I : Ξ ⇒ⁱ Θ ⊕ Γ) → ∀ {A} (t u : Term Ξ Γ A) →
               t ≈ u → [ I ]ⁱ t ≈ [ I ]ⁱ u
  []ⁱ-resp-≈ I t t (≈-≡ refl) = ≈-refl
  []ⁱ-resp-≈ I (tm-meta M ts) (tm-meta M us) (≈-meta ξ) =
    []ˢ-resp-≈ˢ (I M) ([,]ˢ-resp-≈ˢ (λ x → ≈-refl) λ i → []ⁱ-resp-≈ I (ts i) (us i) (ξ i))
  []ⁱ-resp-≈ I (tm-oper f ds) (tm-oper f es) (≈-oper ξ) = ≈-oper λ i → []ⁱ-resp-≈ (⇑ⁱ I) (ds i) (es i) (ξ i)

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
      (≈-sym ([ˢ∘ʳ]ˢ (I M)))
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

  _ʳ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → Γ ⇒ʳ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (ρ ʳ∘ⁱ I) M = [ ⇑ʳ ρ ]ʳ I M

  -- composition of a renaming and an instantiation preerve equality of instantiations

  [ʳ∘ⁱ]ⁱ-resp-≈ⁱ : ∀ {Θ ψ Γ Δ} (ρ : Γ ⇒ʳ Δ) (I J : Θ ⇒ⁱ ψ ⊕ Γ) → (I ≈ⁱ J) → (ρ ʳ∘ⁱ I) ≈ⁱ (ρ ʳ∘ⁱ J)
  [ʳ∘ⁱ]ⁱ-resp-≈ⁱ σ I J ξ M = []ʳ-resp-≈ (ξ M)

  -- composition of a substitution and an instantiation

  _ˢ∘ⁱ_ : ∀ {Θ ψ Γ Δ} → ψ ⊕ Γ ⇒ˢ Δ → Θ ⇒ⁱ ψ ⊕ Γ → Θ ⇒ⁱ ψ ⊕ Δ
  (σ ˢ∘ⁱ I) M = [ ⇑ˢ σ ]ˢ I M

  -- composition of a renaming and an instantiation preserve equality of instantiations

  [ˢ∘ⁱ]ⁱ-resp-≈ⁱ : ∀ {Θ ψ Γ Δ} (σ : ψ ⊕ Γ ⇒ˢ Δ) (I J : Θ ⇒ⁱ ψ ⊕ Γ) → (I ≈ⁱ J) → (σ ˢ∘ⁱ I) ≈ⁱ (σ ˢ∘ⁱ J)
  [ˢ∘ⁱ]ⁱ-resp-≈ⁱ σ I J ξ M = []ˢ-resp-≈ (⇑ˢ σ) (ξ M)

  -- composition of an instantiation and a substitution

  _ⁱ∘ˢ_ : ∀ {Θ ψ Γ Δ} → Θ ⇒ⁱ ψ ⊕ Δ → Θ ⊕ Γ ⇒ˢ Δ →  ψ ⊕ Γ ⇒ˢ Δ
  (I ⁱ∘ˢ σ) x = [ I ]ⁱ σ x

  -- Actions correspondig to the interactions

  -- the action of the identity

  [id]ⁱ : ∀ {Θ Γ A Δ} {t : Term Θ (Γ ,, Δ) A}  → [ idⁱ ]ⁱ t ≈ t
  [id]ⁱ {t = tm-var x} = ≈-refl
  [id]ⁱ {t = tm-meta M ts} = ≈-meta (λ i → [id]ⁱ)
  [id]ⁱ {t = tm-oper f es} = ≈-oper (λ i → [id]ⁱ)


  -- the action of the composition of an instantiation and a renaming

  [ʳ∘ⁱ]ⁱ : ∀ {Θ Ψ Γ Δ A} {ρ : Γ ⇒ʳ Δ} {I : Θ ⇒ⁱ Ψ ⊕ Γ} (t : Term Θ Γ A) →
           [ ρ ]ʳ [ I ]ⁱ t ≈ [ ρ ʳ∘ⁱ I ]ⁱ [ ρ ]ʳ t
  [ʳ∘ⁱ]ⁱ = {!!}

  -- extension commutes with composition

  ⇑ⁱ-resp-∘ⁱ : ∀ {Θ Ξ Ω} {Γ Δ} {I : Θ ⇒ⁱ Ξ ⊕ Γ} {J : Ξ ⇒ⁱ Ω ⊕ Γ} →
               ⇑ⁱ {Δ = Δ} (J ∘ⁱ I) ≈ⁱ ⇑ⁱ J ∘ⁱ ⇑ⁱ I
  ⇑ⁱ-resp-∘ⁱ {I = I} {J = J} M =
    ≈-trans
     ([ʳ∘ⁱ]ⁱ (I M))
     ([]ⁱ-resp-≈ⁱ
        ([ ⇑ʳ var-inl ]ʳ I M)
        (λ N → ≈-trans
                 (≈-sym [∘]ʳ)
                 (≈-trans
                   ([]ʳ-resp-≡ʳ (λ { (var-inl x) → refl ; (var-inr x) → refl }))
                   [∘]ʳ)))

  -- the action of a composition

  [∘]ⁱ : ∀ {Θ Ξ Ω Γ} → {I : Θ ⇒ⁱ Ξ ⊕ Γ} → {J : Ξ ⇒ⁱ Ω ⊕ Γ} →
           ∀ {A} → ∀ (t : Term Θ Γ A) → [ J ∘ⁱ I ]ⁱ t ≈ [ J ]ⁱ [ I ]ⁱ t
  [∘]ⁱ (tm-var x) = ≈-refl
  [∘]ⁱ {I = I} {J = J} (tm-meta M ts) =
    ≈-trans
      ([]ˢ-resp-≈ˢ
        ([ ⇑ⁱ J ]ⁱ (I M))
        ([,]ˢ-resp-≈ˢ (λ x → ≈-refl) (λ i → [∘]ⁱ {I = I} {J = J} (ts i))))
      {!!}
                        -- (≈-trans
                        --   ([]ˢ-resp-≈ˢ
                        --     ([ ⇑ⁱ J ]ⁱ (I M))
                        --     λ x → []ˢ-resp-≈ˢ {σ = [ inlˢ , (λ {A} i → [ J ]ⁱ [ I ]ⁱ ts i) ]ˢ} {τ = λ i → {! (I ⇒ⁱ J ext[ ts ]) i !}} (tm-var x) ({! I ⇒ⁱ J ext[ ts ]-correct !})))
  --              where
  --                _⇒ⁱ_ext[_] : ∀ {Θ ψ Ω Γ Δ Ξ A} (I : Θ ⇒ⁱ ψ ⊕ Γ) (J : ψ ⇒ⁱ Ω ⊕ Γ)
  --                         →  (∀ {B} (i : B ∈ Δ) → Term Θ (Γ ,, Ξ) B)
  --                         → A ∈ Γ ,, Δ → Term Ω (Γ ,, Ξ) A
  --                (I ⇒ⁱ J ext[ ts ]) (var-inl x) = tm-var (var-inl x)
  --                (I ⇒ⁱ J ext[ ts ]) (var-inr x) = [ J ]ⁱ [ I ]ⁱ (ts x)

  --                _⇒ⁱ_ext[_]-correct : ∀ {Θ ψ Ω Γ Δ Ξ}
  --                                      (I : Θ ⇒ⁱ ψ ⊕ Γ) (J : ψ ⇒ⁱ Ω ⊕ Γ)
  --                                      (ts : ∀ {B} (i : B ∈ Δ) → Term Θ (Γ ,, Ξ) B)
  --                                     → ([ inlˢ , (λ i → ( [ J ]ⁱ [ I ]ⁱ (ts i))) ]ˢ) ≈ˢ (λ i → (I ⇒ⁱ J ext[ ts ]) i)
  --                (I ⇒ⁱ J ext[ ts ]-correct) (var-inl i) = ≈-refl
  --                (I ⇒ⁱ J ext[ ts ]-correct) (var-inr i) = ≈-refl
  [∘]ⁱ {I = I} {J = J} (tm-oper f es) =
            ≈-oper (λ i → ≈-trans ([]ⁱ-resp-≈ⁱ (es i) (⇑ⁱ-resp-∘ⁱ {I = I})) ([∘]ⁱ (es i)))

  -- the application of [_]ⁱ_ to an instantiation is a morphism of relative monads
  [_]ⁱ-morphism :  ∀ {Θ ψ Γ} (I : ψ ⇒ⁱ Θ ⊕ Γ) → RMonadMorph (⇑ᵗ-Term-Monad {Θ = Θ} Γ) (⇑ᵗ-Term-Monad {Θ = ψ} Γ)
  [_]ⁱ-morphism = {!!}
                  -- record
                  --   { morph = λ {X = Γ′} A → record { _⟨$⟩_ = λ t → {![ I ]ⁱ ([ inrˢ ]ˢ t)!} ; cong = {!!} }
                  --   ; law-unit = {!!}
                  --   ; law-extend = {!!} }

                  --  RMonadMorph (⇑ᵗ-Term-Monad {Θ = Θ} Γ) (⇑ᵗ-Term-Monad {Θ = ψ} Γ)
                  -- RMonadMorph (Term-Monad {Θ = Θ}) (Term-Monad {Θ = ψ})

    -- -- The embedding of contexts into setoids indexed by sorts

    -- slots : Functor Contexts (IndexedCategory sort (Setoids ℓ ℓ))
    -- slots = record
    --           { F₀ = λ Γ A → setoid (A ∈ Γ)
    --           ; F₁ = λ ρ A → record { _⟨$⟩_ = ρ ; cong = cong ρ }
    --           ; identity = λ A ξ → ξ
    --           ; homomorphism = λ {_} {_} {_} {ρ} {σ} A {_} {_} ξ → cong σ (cong ρ ξ)
    --           ; F-resp-≈ = λ ξ A ζ → trans (ξ _) (cong _ ζ)
    --           }
