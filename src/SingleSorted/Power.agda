open import Agda.Primitive using (_⊔_)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

open import SingleSorted.Context

module SingleSorted.Power
       {o ℓ e}
       (𝒞 : Category.Category o ℓ e) where

  open Category.Category 𝒞
  open HomReasoning

  record Powered (A : Obj) : Set (o ⊔ ℓ ⊔ e) where

    field
      pow : Context → Obj
      π : ∀ {Γ} → var Γ → pow Γ ⇒ A
      tuple : ∀ Γ {B} → (var Γ → B ⇒ A) → B ⇒ pow Γ
      project : ∀ {Γ} {B} {x : var Γ} {fs : var Γ → B ⇒ A} → π x ∘ tuple Γ fs ≈ fs x
      unique : ∀ {Γ} {B} {fs : var Γ → B ⇒ A} {g : B ⇒ pow Γ} → (∀ i → π i ∘ g ≈ fs i) → tuple Γ fs ≈ g

    η : ∀ {Γ} → tuple Γ π ≈ id
    η = unique (λ i → identityʳ)

    ! : ∀ {B : Obj} → B ⇒ pow ctx-empty
    ! = tuple ctx-empty ctx-empty-absurd

    !-unique : ∀ {B : Obj} {f : B ⇒ pow ctx-empty} → ! ≈ f
    !-unique = unique λ i → ctx-empty-absurd i

    !-unique₂ : ∀ {B : Obj} {f g : B ⇒ pow ctx-empty} → f ≈ g
    !-unique₂ = (⟺ !-unique) ○ !-unique

    tuple-cong : ∀ {B : Obj} {Γ} {fs gs : var Γ → B ⇒ A} → (∀ i → fs i ≈ gs i) →
                 tuple Γ fs ≈ tuple Γ gs
    tuple-cong ξ = unique (λ i →  project ○ ⟺ (ξ i))

    ∘-distribʳ-tuple : ∀ {B C} {Γ} {fs : var Γ → B ⇒ A} {g : C ⇒ B}  →
                       tuple Γ (λ x → fs x ∘ g) ≈ tuple Γ fs ∘ g
    ∘-distribʳ-tuple = unique (λ i → ⟺ assoc ○ ∘-resp-≈ˡ project)

  -- A cartesian category has a standard power structure (which we need not use)
  module _ (cartesian-𝒞 : Cartesian.Cartesian 𝒞) (A : Obj) where
    open Cartesian.Cartesian cartesian-𝒞

    standard-pow : Context → Obj
    standard-pow ctx-empty = ⊤
    standard-pow ctx-slot = A
    standard-pow (ctx-concat Γ Δ) = standard-pow Γ × standard-pow Δ

    standard-π : ∀ {Γ} → var Γ → standard-pow Γ ⇒ A
    standard-π var-var = id
    standard-π (var-inl i) = standard-π i ∘ π₁
    standard-π (var-inr i) = standard-π i ∘ π₂

    standard-tuple : ∀ Γ {B} → (var Γ → B ⇒ A) → B ⇒ standard-pow Γ
    standard-tuple ctx-empty fs = !
    standard-tuple ctx-slot fs = fs var-var
    standard-tuple (ctx-concat Γ Δ) fs = ⟨ standard-tuple Γ (λ i → fs (var-inl i)) , standard-tuple Δ (λ j → fs (var-inr j)) ⟩

    standard-project : ∀ {Γ} {B} {x : var Γ} {fs : var Γ → B ⇒ A} →
                       standard-π x ∘ standard-tuple Γ fs ≈ fs x
    standard-project {x = var-var} = identityˡ
    standard-project {x = var-inl x} = assoc ○ ((∘-resp-≈ʳ project₁) ○ standard-project {x = x})
    standard-project {x = var-inr x} = assoc ○ ((∘-resp-≈ʳ project₂) ○ standard-project {x = x})

    standard-unique : ∀ {Γ} {B} {fs : var Γ → B ⇒ A} {g : B ⇒ standard-pow Γ} → (∀ i → standard-π i ∘ g ≈ fs i) →
                      standard-tuple Γ fs ≈ g
    standard-unique {ctx-empty} ξ = !-unique _
    standard-unique {ctx-slot} ξ = ⟺ (ξ var-var) ○ identityˡ
    standard-unique {ctx-concat Γ Δ} {fs = fs} ξ =
      unique
         (⟺ (standard-unique (λ x → sym-assoc ○ (ξ (var-inl x)))))
         (⟺ (standard-unique (λ y → sym-assoc ○ (ξ (var-inr y)))))

    StandardPowered : Powered A
    StandardPowered =
      record
      { pow = standard-pow
      ; π = standard-π
      ; tuple = standard-tuple
      ; project = λ {Γ} → standard-project {Γ}
      ; unique = standard-unique }
