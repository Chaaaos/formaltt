{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Primitive using (_⊔_ ; lsuc ; Level)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Product using (Product)

open import MultiSorted.AlgebraicTheory
open import MultiSorted.Substitution
import MultiSorted.Product as Product
import MultiSorted.Interpretation as Interpretation

module MultiSorted.InterpretationCategory
         {o ℓ e}
         {𝓈 ℴ}
         (Σ : Signature {𝓈} {ℴ})
         {𝒞 : Category.Category o ℓ e}
         (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
  open Signature Σ
  open Category.Category 𝒞
  open Interpretation Σ cartesian-𝒞

  -- Useful shortcuts for levels
  ℓℴ : Level
  ℓℴ = o ⊔ ℓ ⊔ e ⊔ 𝓈 ⊔ ℴ

  ℓ𝓇 : Level
  ℓ𝓇 = e ⊔ 𝓈

  -- Equality of homomorphisms of interpretations
  _≈I_ : ∀ {I J : Interpretation} → HomI I J → HomI I J → Set ℓ𝓇
  _≈I_ {I} {J} ϕ ψ =
                   let open HomI in
                   ∀ (A : sort) → hom-morphism ϕ {A} ≈ hom-morphism ψ


  -- The category of interpretations of Σ in 𝒞
  ℐ𝓃𝓉 : Category.Category ℓℴ ℓℴ ℓ𝓇
  ℐ𝓃𝓉 = record
          { Obj = Interpretation
          ; _⇒_ = HomI
          ; _≈_ = _≈I_
          ; id = λ {A} → IdI A
          ; _∘_ = _∘I_
          ; assoc = λ A → assoc
          ; sym-assoc = λ A → sym-assoc
          ; identityˡ = λ A → identityˡ
          ; identityʳ = λ A → identityʳ
          ; identity² = λ A → identity²
          ; equiv = record { refl = λ A → Equiv.refl
                           ; sym = λ p A → Equiv.sym (p A)
                           ; trans = λ p₁ p₂ A → Equiv.trans (p₁ A) (p₂ A)
                           }
          ; ∘-resp-≈ = λ p₁ p₂ A → ∘-resp-≈ (p₁ A) (p₂ A)
          }

  -- Cartesian structure on the category on interpretations of Σ in 𝒞
  open Cartesian.Cartesian
  open Interpretation.Interpretation

  product-ℐ𝓃𝓉 : ∀ {I J} → Product ℐ𝓃𝓉 I J
  product-ℐ𝓃𝓉 {I = I} {J = J} =
                let open Cartesian.Cartesian in
                let open Interpretation.Interpretation in
                let open Product.Producted in
                let open HomReasoning in
                record
                  { A×B = record
                          { interp-sort = λ A → (cartesian-𝒞 × interp-sort I A) (interp-sort J A)
                          ; interp-ctx = record
                                         { prod = λ Γ → (cartesian-𝒞 × prod (interp-ctx I) Γ) (prod (interp-ctx J) Γ)
                                         ; π = λ {Γ} (x : var Γ) → (cartesian-𝒞 ⁂ π (interp-ctx I) x) (π (interp-ctx J) x)
                                         ; tuple = λ Γ fs → ⟨ cartesian-𝒞 , tuple (interp-ctx I) Γ (λ x → π₁ cartesian-𝒞 ∘ fs x) ⟩ (tuple (interp-ctx J) Γ λ x → (π₂ cartesian-𝒞) ∘ fs x)
                                         ; project = λ {Γ} {B} {x} {fs} → (⁂∘⟨⟩ cartesian-𝒞) ○ ⟨⟩-cong₂ {!!} {!!} {!!}
                                         ; unique = λ x → {!!}
                                         }
                          ; interp-oper = λ f → (cartesian-𝒞 ⁂ interp-oper I f) (interp-oper J f)
                          }
                  ; π₁ = record
                         { hom-morphism = π₁ cartesian-𝒞
                         ; hom-commute = λ f → {!!}}
                  ; π₂ = record
                         { hom-morphism = π₂ cartesian-𝒞
                         ; hom-commute = {!!} }
                  ; ⟨_,_⟩ = λ ϕ ψ → record
                         { hom-morphism = λ {A} → {!!}
                         ; hom-commute = {!!}
                         }
                  ; project₁ = {!!}
                  ; project₂ = {!!}
                  ; unique = {!!}
                  }



  terminal-ℐ𝓃𝓉 : Terminal ℐ𝓃𝓉
  terminal-ℐ𝓃𝓉 = record
                 { ⊤ = Trivial
                 ; ⊤-is-terminal =
                                   let open Cartesian.Cartesian in
                                   record
                                   { ! = record { hom-morphism = ! cartesian-𝒞
                                                ; hom-commute = λ f → {!!}
                                                }
                                   ; !-unique = λ f A → {!!}
                                   }
                 }

  cartesian-ℐ𝓃𝓉 : Cartesian.Cartesian ℐ𝓃𝓉
  cartesian-ℐ𝓃𝓉 = record
                  { terminal = terminal-ℐ𝓃𝓉
                  ; products = record { product = product-ℐ𝓃𝓉 }
                  }
