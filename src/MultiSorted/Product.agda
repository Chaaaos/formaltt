open import Agda.Primitive using (_⊔_)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

open import MultiSorted.AlgebraicTheory

-- Finite products indexed by contexts
module MultiSorted.Product
       {o ℓ e}
       (𝒞 : Category.Category o ℓ e)
       {Σ : Signature}
       (interp-sort : Signature.sort Σ → Category.Category.Obj 𝒞) where

  open Signature Σ
  open Category.Category 𝒞
  open HomReasoning

  interp-sort-var : {Γ : Context} → var Γ → Obj
  interp-sort-var {Γ} x = interp-sort (sort-of Γ x)

  record Producted : Set (o ⊔ ℓ ⊔ e) where

    field
      prod : Context → Obj
      π : ∀ {Γ} (x : var Γ) → prod Γ ⇒ interp-sort-var x
      tuple : ∀ Γ {B} → ((x : var Γ) → B ⇒ interp-sort-var x) → B ⇒ prod Γ
      project : ∀ {Γ} {B} {x : var Γ} {fs : (y : var Γ) → B ⇒ interp-sort-var y} → π x ∘ tuple Γ fs ≈ fs x
      unique : ∀ {Γ} {B} {fs : (x : var Γ) → B ⇒ interp-sort-var x} {g : B ⇒ prod Γ} → (∀ i → π i ∘ g ≈ fs i) → tuple Γ fs ≈ g

    η : ∀ {Γ} → tuple Γ π ≈ id
    η = unique (λ i → identityʳ)

    ! : ∀ {B : Obj} → B ⇒ prod ctx-empty
    ! {B} = tuple ctx-empty ctx-empty-absurd

    !-unique : ∀ {B : Obj} {f : B ⇒ prod ctx-empty} → ! ≈ f
    !-unique {f = f} = unique ctx-empty-absurd

    !-unique₂ : ∀ {B : Obj} {f g : B ⇒ prod ctx-empty} → f ≈ g
    !-unique₂ = (⟺ !-unique) ○ !-unique

    tuple-cong : ∀ {B : Obj} {Γ} {fs gs : (x : var Γ) → B ⇒ interp-sort-var x} → (∀ i → fs i ≈ gs i) →
                 tuple Γ fs ≈ tuple Γ gs
    tuple-cong ξ = unique (λ i →  project ○ ⟺ (ξ i))

    ∘-distribʳ-tuple : ∀ {B C} {Γ} {fs : (x : var Γ) → B ⇒ interp-sort-var x} {g : C ⇒ B}  →
                       tuple Γ (λ x → fs x ∘ g) ≈ tuple Γ fs ∘ g
    ∘-distribʳ-tuple = unique (λ i → ⟺ assoc ○ ∘-resp-≈ˡ project)

  -- A cartesian category has a standard products structure (which we need not use)
  module _ (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
    open Cartesian.Cartesian cartesian-𝒞

    standard-prod : Context → Obj
    standard-prod ctx-empty = ⊤
    standard-prod (ctx-slot A) = interp-sort A
    standard-prod (ctx-concat Γ Δ) = standard-prod Γ × standard-prod Δ

    standard-π : ∀ {Γ} (x : var Γ) → standard-prod Γ ⇒ interp-sort-var x
    standard-π var-var = id
    standard-π (var-inl i) = standard-π i ∘ π₁
    standard-π (var-inr i) = standard-π i ∘ π₂

    standard-tuple : ∀ Γ {B} → ((x : var Γ) → B ⇒ interp-sort-var x) → B ⇒ standard-prod Γ
    standard-tuple ctx-empty fs = !
    standard-tuple (ctx-slot _) fs = fs var-var
    standard-tuple (ctx-concat Γ Δ) fs = ⟨ standard-tuple Γ (λ i → fs (var-inl i)) , standard-tuple Δ (λ j → fs (var-inr j)) ⟩

    standard-project : ∀ {Γ} {B} {x : var Γ} {fs : (x : var Γ) → B ⇒ interp-sort-var x} →
                       standard-π x ∘ standard-tuple Γ fs ≈ fs x
    standard-project {x = var-var} = identityˡ
    standard-project {x = var-inl x} = assoc ○ ((∘-resp-≈ʳ project₁) ○ standard-project {x = x})
    standard-project {x = var-inr x} = assoc ○ ((∘-resp-≈ʳ project₂) ○ standard-project {x = x})

    standard-unique : ∀ {Γ} {B} {fs : (x : var Γ) → B ⇒ interp-sort-var x} {g : B ⇒ standard-prod Γ} → (∀ i → standard-π i ∘ g ≈ fs i) →
                      standard-tuple Γ fs ≈ g
    standard-unique {ctx-empty} ξ = !-unique _
    standard-unique {ctx-slot _} ξ = ⟺ (ξ var-var) ○ identityˡ
    standard-unique {ctx-concat Γ Δ} {fs = fs} ξ =
      unique
         (⟺ (standard-unique (λ x → sym-assoc ○ (ξ (var-inl x)))))
         (⟺ (standard-unique (λ y → sym-assoc ○ (ξ (var-inr y)))))

    StandardProducted : Producted
    StandardProducted =
      record
      { prod = standard-prod
      ; π = standard-π
      ; tuple = standard-tuple
      ; project = λ {Γ} → standard-project {Γ}
      ; unique = standard-unique }
