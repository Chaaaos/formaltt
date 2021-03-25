{-#  OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc)

open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as SetoidR

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Product using (Product)

open import MultiSorted.AlgebraicTheory
import MultiSorted.Substitution as Substitution
import MultiSorted.Product as Product

module MultiSorted.SyntacticCategory
  {ℓt}
  {Σ : Signature}
  (T : Theory ℓt Σ) where

  open Theory T
  open Substitution T

  -- The syntactic category

  𝒮 : Category.Category lzero lzero (lsuc ℓt)
  𝒮 =
    record
      { Obj = Context
      ; _⇒_ = _⇒s_
      ; _≈_ = _≈s_
      ; id =  id-s
      ; _∘_ =  _∘s_
      ; assoc = λ {_ _ _ _ _ _ σ} x → subst-∘s (σ x)
      ; sym-assoc =  λ {_ _ _ _ _ _ σ} x → eq-symm (subst-∘s (σ x))
      ; identityˡ = λ x → eq-refl
      ; identityʳ = λ {A B f} x → tm-var-id
      ; identity² = λ x → eq-refl
      ; equiv = record
                 { refl = λ x → eq-refl
                 ; sym = λ ξ y → eq-symm (ξ y)
                 ; trans = λ ζ ξ y → eq-tran (ζ y) (ξ y)}
      ; ∘-resp-≈ = ∘s-resp-≈s
      }

  -- I don't think the name of the following property is the best, I did not fine a better one for the moment
  interp-resp-sort : ∀ {Γ} {x : var Γ} {y} →  Term Γ (sort-of Γ x) → Term Γ (sort-of (Product.interp-sort-var 𝒮 {Σ = Σ} ctx-slot x) y)
  interp-resp-sort {y = var-var} = λ t → t

  -- We use the power structure which gives back the context directly
  π-𝒮 : ∀ {Γ} (x : var Γ) → Γ ⇒s ctx-slot (sort-of Γ x)
  π-𝒮 x var-var = tm-var x

  tuple-𝒮 : ∀ Γ {Δ} → (∀ (x : var Γ) → Δ ⇒s (ctx-slot (sort-of Γ x))) → Δ ⇒s Γ
  tuple-𝒮 Γ ts = λ x → ts x var-var

  project-𝒮 : ∀ {Γ Δ} {x : var Γ} {ts : ∀ (x : var Γ) → Δ ⇒s (ctx-slot (sort-of Γ x))} →
              π-𝒮 x ∘s tuple-𝒮 Γ ts ≈s ts x
  project-𝒮 {Γ} {Δ} {x} {ts} var-var = eq-refl

  unique-𝒮 : ∀ {Γ Δ} {ts : ∀ (x : var Γ) → Δ ⇒s (ctx-slot (sort-of Γ x))} {g : Δ ⇒s Γ} →
             (∀ x → π-𝒮 x ∘s g ≈s ts x) → tuple-𝒮 Γ ts ≈s g
  unique-𝒮 ξ x = eq-symm (ξ x var-var)


  producted-𝒮 : Product.Producted 𝒮 {Σ = Σ} ctx-slot
  producted-𝒮 =
    record
      { prod = λ Γ → Γ
      ; π =  π-𝒮
      ; tuple = tuple-𝒮
      ; project = λ {Γ Δ x ts} → project-𝒮 {ts = ts}
      ; unique = unique-𝒮
      }

  -- The terminal object is the empty context
  ⊤-𝒮 : Context
  ⊤-𝒮 = ctx-empty

  !-𝒮 : ∀ {Γ} → Γ ⇒s ⊤-𝒮
  !-𝒮 ()

  !-unique-𝒮 : ∀ {Γ} (σ : Γ ⇒s ⊤-𝒮) → !-𝒮 ≈s σ
  !-unique-𝒮 σ ()

  terminal-𝒮 : Terminal 𝒮
  terminal-𝒮 =
    record
      { ⊤ = ⊤-𝒮
      ; ⊤-is-terminal =
          record { ! = !-𝒮
                 ; !-unique = !-unique-𝒮 } }

  -- Binary product is context contatenation
  product-𝒮 : ∀ {Γ Δ} → Product 𝒮 Γ Δ
  product-𝒮 {Γ} {Δ} =
    record
      { A×B =  ctx-concat Γ Δ
      ; π₁ = λ x → tm-var (var-inl x)
      ; π₂ = λ x → tm-var (var-inr x)
      ; ⟨_,_⟩ = ⟨_,_⟩s
      ; project₁ = λ x → eq-refl
      ; project₂ = λ x → eq-refl
      ; unique = λ {Θ σ σ₁ σ₂} ξ₁ ξ₂ z → u Θ σ σ₁ σ₂ ξ₁ ξ₂ z
      }
    where u : ∀ Θ (σ : Θ ⇒s ctx-concat Γ Δ) (σ₁ : Θ ⇒s Γ) (σ₂ : Θ ⇒s Δ) →
                  ((λ x → σ (var-inl x)) ≈s σ₁) → ((λ y → σ (var-inr y)) ≈s σ₂) → ⟨ σ₁ , σ₂ ⟩s ≈s σ
          u Θ σ σ₁ σ₂ ξ₁ ξ₂ (var-inl z) = eq-symm (ξ₁ z)
          u Θ σ σ₁ σ₂ ξ₁ ξ₂ (var-inr z) = eq-symm (ξ₂ z)

  -- The cartesian structure of the syntactic category
  cartesian-𝒮 : Cartesian.Cartesian 𝒮
  cartesian-𝒮 =
    record
      { terminal = terminal-𝒮
      ; products = record { product = product-𝒮 } }
