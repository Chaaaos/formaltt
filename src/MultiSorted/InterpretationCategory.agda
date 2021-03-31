{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Primitive using (_⊔_ ; lsuc ; Level)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Product using (Product)

open import MultiSorted.AlgebraicTheory
import MultiSorted.Product as Product
import MultiSorted.Interpretation

module MultiSorted.InterpretationCategory
         {o ℓ e}
         {𝓈 ℴ}
         (Σ : Signature {𝓈} {ℴ})
         {𝒞 : Category.Category o ℓ e}
         (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
  open Signature Σ
  open Category.Category 𝒞
  open Cartesian.Cartesian cartesian-𝒞
  open MultiSorted.Interpretation Σ cartesian-𝒞

  -- Equality of homomorphisms of interpretations
  _≈I_ : ∀ {I J : Interpretation} → I ⇒I J → I ⇒I J → Set (e ⊔ 𝓈)
  _≈I_ {I} {J} ϕ ψ =
    let open _⇒I_ in ∀ (A : sort) → hom-morphism ϕ {A} ≈ hom-morphism ψ


  -- The category of interpretations of Σ in 𝒞
  ℐ𝓃𝓉 : Category.Category (o ⊔ ℓ ⊔ e ⊔ 𝓈 ⊔ ℴ) (o ⊔ ℓ ⊔ e ⊔ 𝓈 ⊔ ℴ) (e ⊔ 𝓈)
  ℐ𝓃𝓉 = record
          { Obj = Interpretation
          ; _⇒_ = _⇒I_
          ; _≈_ = _≈I_
          ; id = id-I
          ; _∘_ = _∘I_
          ; assoc = λ _ → assoc
          ; sym-assoc = λ _ → sym-assoc
          ; identityˡ = λ _ → identityˡ
          ; identityʳ = λ _ → identityʳ
          ; identity² = λ _ → identity²
          ; equiv = record { refl = λ A → Equiv.refl
                           ; sym = λ p A → Equiv.sym (p A)
                           ; trans = λ p₁ p₂ A → Equiv.trans (p₁ A) (p₂ A)
                           }
          ; ∘-resp-≈ = λ p₁ p₂ A → ∘-resp-≈ (p₁ A) (p₂ A)
          }

  -- Cartesian structure on the category on interpretations of Σ in 𝒞

  A×B-ℐ𝓃𝓉 : Interpretation → Interpretation → Interpretation
  A×B-ℐ𝓃𝓉 I J =
    let open Product.Producted in
    let open Interpretation in
    record
      { interp-sort = λ A → interp-sort I A × interp-sort J A
      ; interp-ctx =
          record
            { prod = λ Γ → prod (interp-ctx I) Γ × prod (interp-ctx J) Γ
            ; π = λ {Γ} x → (π (interp-ctx I) x) ⁂ (π (interp-ctx J) x)
            ; tuple = λ Γ fs → ⟨ (tuple (interp-ctx I) Γ λ x → π₁ ∘ fs x) , ((tuple (interp-ctx J) Γ λ x → π₂ ∘ fs x)) ⟩
            ; project = {!!}
            ; unique = {!!}
            }
      ; interp-oper = λ f → (interp-oper I f) ⁂ (interp-oper J f)
      }

  π₁-ℐ𝓃𝓉 : ∀ {I J : Interpretation} → A×B-ℐ𝓃𝓉 I J ⇒I I
  π₁-ℐ𝓃𝓉 {I} {J} = {!!}

  π₂-ℐ𝓃𝓉 : ∀ {I J : Interpretation} → A×B-ℐ𝓃𝓉 I J ⇒I J
  π₂-ℐ𝓃𝓉 {I} {J} = {!!}

  ⟨_,_⟩-ℐ𝓃𝓉 : ∀ {I J K : Interpretation} → I ⇒I J → I ⇒I K → I ⇒I A×B-ℐ𝓃𝓉 J K
  ⟨ ϕ , ψ ⟩-ℐ𝓃𝓉 =
     record
       { hom-morphism = λ {A} → {!!}
       ; hom-commute = {!!}
       }

  project₁-ℐ𝓃𝓉 : Category.Category.Obj 𝒞
  project₁-ℐ𝓃𝓉 = Terminal.⊤ (Cartesian.Cartesian.terminal cartesian-𝒞)

  project₂-ℐ𝓃𝓉 : {!!}
  project₂-ℐ𝓃𝓉 = {!!}

  unique-ℐ𝓃𝓉 : {!!}
  unique-ℐ𝓃𝓉 = {!!}

  product-ℐ𝓃𝓉 : ∀ {I J} → Product ℐ𝓃𝓉 I J
  product-ℐ𝓃𝓉 {I} {J} =
    record
      { A×B = A×B-ℐ𝓃𝓉 I J
      ; π₁ = π₁-ℐ𝓃𝓉 {I} {J}
      ; π₂ = π₂-ℐ𝓃𝓉 {I} {J}
      ; ⟨_,_⟩ = ⟨_,_⟩-ℐ𝓃𝓉
      ; project₁ = {! project₂-ℐ𝓃𝓉 !}
      ; project₂ = {! project₂-ℐ𝓃𝓉 !}
      ; unique = {! unique-ℐ𝓃𝓉 !}
      }

  terminal-ℐ𝓃𝓉 : Terminal ℐ𝓃𝓉
  terminal-ℐ𝓃𝓉 =
    record
      { ⊤ = Trivial
      ; ⊤-is-terminal =
        record
          { ! =
              record
                { hom-morphism = !
                ; hom-commute =  λ f → !-unique₂
                }
          ; !-unique = λ f A → !-unique₂
          }
      }

  cartesian-ℐ𝓃𝓉 : Cartesian.Cartesian ℐ𝓃𝓉
  cartesian-ℐ𝓃𝓉 =
    record
      { terminal = terminal-ℐ𝓃𝓉
      ; products = record { product = product-ℐ𝓃𝓉 }
      }
