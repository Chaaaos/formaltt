open import Agda.Primitive using (lzero; lsuc)

open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as SetoidR

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Product using (Product)

open import SingleSorted.AlgebraicTheory
import SingleSorted.Substitution as Substitution
import SingleSorted.Power as Power

module SingleSorted.SyntacticCategory
  {ℓt}
  {Σ : Signature}
  (T : Theory ℓt Σ) where

  open Signature Σ
  open Theory T
  open Substitution T

  -- The syntactic category

  𝒮 : Category.Category lzero lzero (lsuc ℓt)
  𝒮 =
    record
      { Obj = Context
      ; _⇒_ = substitution Σ
      ; _≈_ = _≈s_
      ; id =  id-substitution
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


  -- We use the power structure which gives back the context directly
  power-𝒮 : Power.Powered 𝒮 ctx-slot
  power-𝒮 =
    record
      { pow = λ Γ → Γ
      ; π = λ x _ → tm-var x
      ; tuple = λ Γ {Δ} ts x → ts x var-var
      ; project = λ {Γ} {Δ} {x} {fs} y → ≡-⊢-≈ (cong₂ fs refl var-var-unique)
      ; unique = λ {Δ} {fs} {σ} {ts} ξ x → eq-symm (ξ x var-var)
      }
    where var-var-unique : ∀ {x : var ctx-slot} → var-var ≡ x
          var-var-unique {var-var} = refl

  -- The terminal object is the empty context
  terminal-𝒮 : Terminal 𝒮
  terminal-𝒮 =
    record
      { ⊤ = ctx-empty
      ; ⊤-is-terminal =
          record { ! = ctx-empty-absurd
                 ; !-unique = λ σ x → ctx-empty-absurd x } }

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
    where u : ∀ Θ (σ : substitution Σ Θ (ctx-concat Γ Δ)) (σ₁ : substitution Σ Θ Γ) (σ₂ : substitution Σ Θ Δ) →
                  ((λ x → σ (var-inl x)) ≈s σ₁) → ((λ y → σ (var-inr y)) ≈s σ₂) → ⟨ σ₁ , σ₂ ⟩s ≈s σ
          u Θ σ σ₁ σ₂ ξ₁ ξ₂ (var-inl z) = eq-symm (ξ₁ z)
          u Θ σ σ₁ σ₂ ξ₁ ξ₂ (var-inr z) = eq-symm (ξ₂ z)

  -- The cartesian structure of the syntactic category
  cartesian-𝒮 : Cartesian.Cartesian 𝒮
  cartesian-𝒮 =
    record
      { terminal = terminal-𝒮
      ; products = record { product = product-𝒮 } }
