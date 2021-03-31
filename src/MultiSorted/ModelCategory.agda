open import Agda.Primitive using (_⊔_ ; lsuc ; Level)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Product using (Product)

open import MultiSorted.AlgebraicTheory
open import MultiSorted.Substitution
import MultiSorted.Product as Product
import MultiSorted.Interpretation as Interpretation
import MultiSorted.Model as Model
import MultiSorted.InterpretationCategory as InterpretationCategory

module MultiSorted.ModelCategory
         {ℓt o ℓ e}
         {𝓈 ℴ}
         {Σ : Signature {𝓈} {ℴ}}
         (T : Theory ℓt Σ)
         {𝒞 : Category.Category o ℓ e}
         (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
  open Signature Σ
  open Theory T
  open Category.Category 𝒞
  open Interpretation Σ cartesian-𝒞
  open Model {o = o} {ℓ = ℓ} {e = e} {Σ = Σ} T

  -- Useful shortcuts for levels
  ℓℴ : Level
  ℓℴ = lsuc (o ⊔ ℓ ⊔ e ⊔ 𝓈 ⊔ ℴ ⊔ ℓt)

  ℓ𝒽 : Level
  ℓ𝒽 = ℓ ⊔ o ⊔ e ⊔ 𝓈 ⊔ ℴ

  ℓ𝓇 : Level
  ℓ𝓇 = e ⊔ 𝓈

  -- New definition of models
  record ⋆Model : Set ℓℴ where
    field
      interpretation : Interpretation
      proof-model : Model.Model T interpretation

  open ⋆Model

  -- Homomorphisms of models
  HomM : ∀ (M N : ⋆Model) → Set ℓ𝒽
  HomM M N = HomI (interpretation M) (interpretation N)

  -- Equality of homomorphisms of models (the same as for the interpretations)
  _≈M_ : ∀ {M N : ⋆Model} → HomM M N → HomM M N → Set ℓ𝓇
  _≈M_ {M} {N} ϕ ψ =
                   let open HomI in
                   ∀ A → (hom-morphism ϕ {A}) ≈ (hom-morphism ψ)

  -- The identity morphism on models
  IdM : (M : ⋆Model) → HomM M M
  IdM = λ M → IdI (interpretation M)

  -- Composition of morphisms of Models
  _∘M_ : ∀ {M N O : ⋆Model} → HomM N O → HomM M N → HomM M O
  _∘M_ ϕ ψ = ϕ ∘I ψ


  -- The category of Models of Σ in 𝒞
  ℳ : Category.Category ℓℴ ℓ𝒽 ℓ𝓇
  ℳ = record
          { Obj = ⋆Model
          ; _⇒_ = HomM
          ; _≈_ = λ {M} {N} ϕ ψ → _≈M_ {M} {N} ϕ ψ
          ; id = λ {M} → IdM M
          ; _∘_ = λ {M} {N} {O} ϕ ψ → _∘M_ {M} {N} {O} ϕ ψ
          ; assoc = λ A → assoc -- λ A → assoc
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
  -- The category of models ℳ (T, 𝒞) is (isomorphic to) a full subcategory of ℐ𝓃𝓉 (Σ , 𝒞)

  -- The product of ℐ𝓃𝓉 carries over the models
