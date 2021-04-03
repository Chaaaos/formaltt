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
  _⇒M_ : ∀ (M N : ⋆Model) → Set ℓ𝒽
  _⇒M_ M N = (interpretation M) ⇒I (interpretation N)

  -- Equality of homomorphisms of models (the same as for the interpretations)
  _≈M_ : ∀ {M N : ⋆Model} → M ⇒M N → M ⇒M N → Set ℓ𝓇
  _≈M_ {M} {N} ϕ ψ =
                   let open _⇒I_ in
                   ∀ A → (hom-morphism ϕ {A}) ≈ (hom-morphism ψ)

  -- The identity morphism on models
  id-M : (M : ⋆Model) → M ⇒M M
  id-M = λ M → id-I {interpretation M}

  -- Composition of morphisms of Models
  _∘M_ : ∀ {M N O : ⋆Model} →  N ⇒M O → M ⇒M N → M ⇒M O
  _∘M_ ϕ ψ = ϕ ∘I ψ


  -- The category of Models of Σ in 𝒞
  ℳ : Category.Category ℓℴ ℓ𝒽 ℓ𝓇
  ℳ = record
          { Obj = ⋆Model
          ; _⇒_ = _⇒M_
          ; _≈_ = λ {M} {N} ϕ ψ → _≈M_ {M} {N} ϕ ψ
          ; id = λ {M} → id-M M
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

  -- The product of "Model proofs"

  module _ (M N : ⋆Model) where
    open Product.Producted
    open HomReasoning
    open InterpretationCategory
    open Cartesian.Cartesian cartesian-𝒞
    open Interpretation.Interpretation
    open import Categories.Object.Product.Morphisms {o} {ℓ} {e} 𝒞
    open Equation

    proof-model-pairs : ∀ ε → (interp-term (interpretation M) (Equation.eq-lhs (ax-eq ε)) ⁂  interp-term (interpretation N) (Equation.eq-lhs (ax-eq ε)))
                               ≈ (interp-term (interpretation M) (Equation.eq-rhs (ax-eq ε)) ⁂  interp-term (interpretation N) (Equation.eq-rhs (ax-eq ε))) →
                               Interpretation.interp-term (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N)) (Equation.eq-lhs (ax-eq ε))
                               ≈ Interpretation.interp-term (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N)) (Equation.eq-rhs (ax-eq ε))
    proof-model-pairs ε p =
                            begin
                              Interpretation.interp-term
                                (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N))
                                (Equation.eq-lhs (ax-eq ε)) ≈⟨ ⟺
                                                                 (Cartesian.Cartesian.unique cartesian-𝒞
                                                                   (natural-π₁ Σ cartesian-𝒞 {I = interpretation M} {interpretation N} (ax-lhs ε))
                                                                   (natural-π₂ Σ cartesian-𝒞 {I = interpretation M} {interpretation N} (ax-lhs ε))) ⟩
                              product.⟨
                                Interpretation.interp-term (interpretation M) (eq-lhs (ax-eq ε)) ∘
                                π₁
                                ,
                                Interpretation.interp-term (interpretation N) (eq-lhs (ax-eq ε)) ∘
                                π₂
                                ⟩ ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ˡ (Model.model-eq (proof-model M) ε)) (∘-resp-≈ˡ (Model.model-eq (proof-model N) ε)) ⟩
                              product.⟨
                                Interpretation.interp-term (interpretation M) (eq-rhs (ax-eq ε)) ∘
                                π₁
                                ,
                                Interpretation.interp-term (interpretation N) (eq-rhs (ax-eq ε)) ∘
                                π₂
                                ⟩ ≈⟨ Cartesian.Cartesian.unique cartesian-𝒞
                                     (natural-π₁ Σ cartesian-𝒞 {I = interpretation M} {interpretation N} (ax-rhs ε))
                                     (natural-π₂ Σ cartesian-𝒞 {I = interpretation M} {interpretation N} (ax-rhs ε)) ⟩
                              Interpretation.interp-term
                                (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N))
                                (eq-rhs (ax-eq ε)) ∎


    proof-model-product : Model (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N))
    Model.model-eq proof-model-product ε =
                                           begin
                                             Interpretation.interp-term
                                               (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N))
                                               (Equation.eq-lhs (ax-eq ε)) ≈⟨ proof-model-pairs ε (⁂-cong₂ (Model.model-eq (proof-model M) ε) (Model.model-eq (proof-model N) ε)) ⟩
                                             Interpretation.interp-term
                                               (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N))
                                               (Equation.eq-rhs (ax-eq ε)) ∎

  -- The product of ℐ𝓃𝓉 carries over the models : the product of two models is a model
  module _ (M N : ⋆Model) where
    open Product.Producted
    open HomReasoning
    open InterpretationCategory
    A×B-ℳ : ⋆Model
    A×B-ℳ = record
              { interpretation = A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N)
              ; proof-model = proof-model-product M N
              }


   -- The cartesian structure of the category of models
  open InterpretationCategory Σ cartesian-𝒞

  π₁-ℳ : ∀ {M N : ⋆Model} → A×B-ℳ M N ⇒M M
  π₁-ℳ {M} {N} = π₁-ℐ𝓃𝓉 {interpretation M} {interpretation N}

  π₂-ℳ : ∀ {M N : ⋆Model} → A×B-ℳ M N ⇒M N
  π₂-ℳ {M} {N} = π₂-ℐ𝓃𝓉 {interpretation M} {interpretation N}

  ⟨_,_⟩-ℳ : ∀ {M N O : ⋆Model} → M ⇒M N → M ⇒M O → M ⇒M A×B-ℳ N O
  ⟨_,_⟩-ℳ {M} {N} {O} ϕ ψ = ⟨ ϕ , ψ ⟩-ℐ𝓃𝓉

  project₁-ℳ : {M N O : ⋆Model} {h : M ⇒M N} {i : M ⇒M O} → _≈M_ {M} {N} (π₁-ℐ𝓃𝓉 {interpretation N} {interpretation O} ∘I ⟨ h , i ⟩-ℐ𝓃𝓉) h
  project₁-ℳ {M} {N} {O} {h} {i} A = project₁-ℐ𝓃𝓉 {interpretation M} {interpretation N} {interpretation O} {h} {i} A

  project₂-ℳ : {M N O : ⋆Model} {h : M ⇒M N} {i : M ⇒M O} → _≈M_ {M} {O} (π₂-ℐ𝓃𝓉 {interpretation N} {interpretation O} ∘I ⟨ h , i ⟩-ℐ𝓃𝓉) i
  project₂-ℳ {M} {N} {O} {h} {i} A = project₂-ℐ𝓃𝓉 {interpretation M} {interpretation N} {interpretation O} {h} {i} A

  unique-ℳ : {M N O : ⋆Model} {h : M ⇒M A×B-ℳ N O} {i : M ⇒M N} {j : M ⇒M O} → _≈M_ {M} {N} (π₁-ℐ𝓃𝓉 {interpretation N} {interpretation O} ∘I h) i → _≈M_ {M} {O} (π₂-ℐ𝓃𝓉 {interpretation N} {interpretation O} ∘I h) j → _≈M_ {M} {A×B-ℳ N O} ⟨ i , j ⟩-ℐ𝓃𝓉 h
  unique-ℳ {M} {N} {O} {h} {i} {j} p₁ p₂ = unique-ℐ𝓃𝓉 {interpretation M} {interpretation N} {interpretation O} {h} {i} {j} (λ A → p₁ A) λ A → p₂ A

  product-ℳ : ∀ {M N} → Product ℳ M N
  product-ℳ {M} {N} =
    record
      { A×B = A×B-ℳ M N
      ; π₁ = π₁-ℳ {M} {N}
      ; π₂ = π₂-ℳ {M} {N}
      ; ⟨_,_⟩ = λ {O} → ⟨_,_⟩-ℳ {O} {M} {N}
      ; project₁ = λ {O} {h} {i} A → project₁-ℳ {O} {M} {N} {h} {i} A
      ; project₂ = λ {O} {h} {i} A → project₂-ℳ {O} {M} {N} {h} {i} A
      ; unique = λ {O} {h} {i} {j} p₁ p₂ A → unique-ℳ {O} {M} {N} {h} {i} {j} p₁ p₂ A
      }
