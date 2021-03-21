{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Nat
open import Data.Fin

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

open import SingleSorted.AlgebraicTheory

module SingleSorted.FactsCartesian
       {o ℓ e}
       {𝒞 : Category.Category o ℓ e}
       (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
  open Category.Category 𝒞
  open Cartesian.Cartesian cartesian-𝒞 public
  open HomReasoning

  -- Power by a context
  pow : ∀ (A : Obj) (Γ : Context) → Obj
  pow A ctx-empty = ⊤
  pow A ctx-slot = A
  pow A (ctx-concat Γ Δ) = pow A Γ × pow A Δ

  pow-π : ∀ {A : Obj} {Γ : Context} (i : var Γ) → pow A Γ ⇒ A
  pow-π {A} var-var = id
  pow-π {A} (var-inl i) = pow-π i ∘ π₁
  pow-π {A} (var-inr i) = pow-π i ∘ π₂

  -- We make the argument n explicit because Agda has a hard time telling what it is
  -- by looking at the function.
  pow-tuple : ∀ {A B : Obj} (Γ : Context) → (var Γ → A ⇒ B) → A ⇒ pow B Γ
  pow-tuple ctx-empty fs =  !
  pow-tuple ctx-slot fs = fs var-var
  pow-tuple (ctx-concat Γ Δ) fs = ⟨ pow-tuple Γ (λ i → fs (var-inl i)) , pow-tuple Δ (λ j → fs (var-inr j)) ⟩


  pow-tuple-∘ : ∀ {A B C : Obj} {Γ : Context} {fs : var Γ → B ⇒ C} {g : A ⇒ B} →
                pow-tuple Γ (λ i → fs i ∘ g) ≈ pow-tuple Γ fs ∘ g
  pow-tuple-∘ {Γ = ctx-empty} {fs} {g} = !-unique (! ∘ g)

  pow-tuple-∘ {Γ = ctx-slot} {fs} {g} = Equiv.refl

  pow-tuple-∘ {Γ = ctx-concat Γ Δ} {fs} {g} =
      begin
      pow-tuple (ctx-concat Γ Δ) (λ i → fs i ∘ g) ≈⟨ ⟨⟩-cong₂
                                                       (pow-tuple-∘ {fs = λ i → fs (var-inl i)})
                                                       (pow-tuple-∘ {fs = λ i → fs (var-inr i)}) ⟩
      ⟨ pow-tuple Γ (λ i → fs (var-inl i)) ∘ g , pow-tuple Δ (λ i → fs (var-inr i)) ∘ g ⟩
                                                  ≈˘⟨ ⟨⟩∘ ⟩
      pow-tuple (ctx-concat Γ Δ) fs ∘ g ∎

  pow-tuple-id : ∀ {A : Obj} {Γ} → pow-tuple {A = pow A Γ} Γ pow-π ≈ id
  pow-tuple-id {Γ = ctx-empty} =  !-unique₂
  pow-tuple-id {Γ = ctx-slot} =  Equiv.refl
  pow-tuple-id {Γ = ctx-concat Γ Δ} =
     ⟨⟩-cong₂
        (pow-tuple-∘ {Γ = Γ} ○ (∘-resp-≈ˡ (pow-tuple-id {Γ = Γ}) ○ identityˡ))
        (pow-tuple-∘ {Γ = Δ} ○ (∘-resp-≈ˡ (pow-tuple-id {Γ = Δ}) ○ identityˡ))
     ○ η

  pow-tuple-eq :  ∀ {A B : Obj} {Γ} {fs gs : var Γ → A ⇒ B} → (∀ i → fs i ≈ gs i) →
                  pow-tuple Γ fs ≈ pow-tuple Γ gs
  pow-tuple-eq {Γ = ctx-empty} ξ = !-unique₂
  pow-tuple-eq {Γ = ctx-slot} ξ = ξ var-var
  pow-tuple-eq {Γ = ctx-concat Γ Δ} ξ =
    ⟨⟩-cong₂
      (pow-tuple-eq (λ i → ξ (var-inl i)))
      (pow-tuple-eq (λ j → ξ (var-inr j)))

  pow-tuple-id2 : ∀ {A : Obj} {Γ} {f : var Γ → pow A Γ ⇒ A} → (∀ i → f i ≈ pow-π i) → pow-tuple Γ f ≈ id
  pow-tuple-id2 {A} {Γ} {f} ξ = pow-tuple-eq ξ ○ (pow-tuple-id {A = A} {Γ = Γ})

  pow-π-tuple : ∀ {A B : Obj} {Γ} {fs : var Γ → A ⇒ B} {i : var Γ} →
                (pow-π i ∘ pow-tuple Γ fs) ≈ fs i
  pow-π-tuple {i = var-var} = identityˡ
  pow-π-tuple {Γ = ctx-concat Γ Δ} {fs = fs} {i = var-inl i} =
    begin
    ((pow-π i ∘ π₁) ∘ pow-tuple (ctx-concat Γ Δ) fs) ≈⟨ assoc ⟩
    (pow-π i ∘ π₁ ∘ pow-tuple (ctx-concat Γ Δ) fs)  ≈⟨ refl⟩∘⟨ project₁ ⟩
    (pow-π i ∘ pow-tuple Γ (λ j → fs (var-inl j))) ≈⟨ pow-π-tuple {fs = λ j → fs (var-inl j)} {i = i} ⟩
    fs (var-inl i) ∎

  pow-π-tuple {Γ = ctx-concat Γ Δ} {fs = fs} {i = var-inr i} =
    begin
    ((pow-π i ∘ π₂) ∘ pow-tuple (ctx-concat Γ Δ) fs) ≈⟨ assoc ⟩
    (pow-π i ∘ π₂ ∘ pow-tuple (ctx-concat Γ Δ) fs)  ≈⟨ refl⟩∘⟨ project₂ ⟩
    (pow-π i ∘ pow-tuple Δ (λ j → fs (var-inr j))) ≈⟨ pow-π-tuple {fs = λ j → fs (var-inr j)} {i = i} ⟩
    fs (var-inr i) ∎
