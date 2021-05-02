open import Agda.Primitive using (_⊔_ ; lsuc ; Level)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Product using (Product)

open import MultiSorted.AlgebraicTheory
open import MultiSorted.Substitution
import MultiSorted.Product as Product
import MultiSorted.Interpretation as Interpretation
import MultiSorted.Model as Is-Model
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
  open Is-Model {o = o} {ℓ = ℓ} {e = e} {Σ = Σ} T

  -- Useful shortcuts for levels
  ℓℴ : Level
  ℓℴ = lsuc (o ⊔ ℓ ⊔ e ⊔ 𝓈 ⊔ ℴ ⊔ ℓt)

  ℓ𝒽 : Level
  ℓ𝒽 = ℓ ⊔ o ⊔ e ⊔ 𝓈 ⊔ ℴ

  ℓ𝓇 : Level
  ℓ𝓇 = e ⊔ 𝓈

  -- New definition of models (as a set, not only a property of interpretations)
  record Model : Set ℓℴ where
    field
      interpretation : Interpretation
      is-model : Is-Model.Is-Model T interpretation

  open Model

  -- Homomorphisms of models
  _⇒M_ : ∀ (M N : Model) → Set ℓ𝒽
  _⇒M_ M N = (interpretation M) ⇒I (interpretation N)

  -- Equality of homomorphisms of models (the same as for the interpretations)
  _≈M_ : ∀ {M N : Model} → M ⇒M N → M ⇒M N → Set ℓ𝓇
  _≈M_ {M} {N} ϕ ψ =
                   let open _⇒I_ in
                   ∀ A → (hom-morphism ϕ {A}) ≈ (hom-morphism ψ)

  -- The identity morphism on models
  id-M : (M : Model) → M ⇒M M
  id-M = λ M → id-I {interpretation M}

  -- Composition of morphisms of Models
  _∘M_ : ∀ {M N O : Model} →  N ⇒M O → M ⇒M N → M ⇒M O
  _∘M_ ϕ ψ = ϕ ∘I ψ


  -- The category of Models of Σ in 𝒞
  ℳ : Category.Category ℓℴ ℓ𝒽 ℓ𝓇
  ℳ = record
          { Obj = Model
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

  -- The product of "Model proofs"

  module _ (M N : Model) where
    open Product.Producted
    open HomReasoning
    open InterpretationCategory
    open Cartesian.Cartesian cartesian-𝒞
    open Interpretation.Interpretation
    open import Categories.Object.Product.Morphisms {o} {ℓ} {e} 𝒞
    open Equation

    -- A proof that an axiom holds in a product interpretation amounts to a apir of proofs that the axiom holds in each model
    is-model-pairs : ∀ ε → (interp-term (interpretation M) (Equation.eq-lhs (ax-eq ε)) ⁂  interp-term (interpretation N) (Equation.eq-lhs (ax-eq ε)))
                               ≈ (interp-term (interpretation M) (Equation.eq-rhs (ax-eq ε)) ⁂  interp-term (interpretation N) (Equation.eq-rhs (ax-eq ε))) →
                               Interpretation.interp-term (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N)) (Equation.eq-lhs (ax-eq ε))
                               ≈ Interpretation.interp-term (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N)) (Equation.eq-rhs (ax-eq ε))
    is-model-pairs ε p =
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
                                ⟩ ≈⟨ ⟨⟩-cong₂ (∘-resp-≈ˡ (Is-Model.model-eq (is-model M) ε)) (∘-resp-≈ˡ (Is-Model.model-eq (is-model N) ε)) ⟩
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

    -- The proof that the product interpetation of two models is a model
    is-model-product : Is-Model (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N))
    Is-Model.model-eq is-model-product ε =
                                           begin
                                             Interpretation.interp-term
                                               (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N))
                                               (Equation.eq-lhs (ax-eq ε)) ≈⟨ is-model-pairs ε (⁂-cong₂ (Is-Model.model-eq (is-model M) ε) (Is-Model.model-eq (is-model N) ε)) ⟩
                                             Interpretation.interp-term
                                               (A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N))
                                               (Equation.eq-rhs (ax-eq ε)) ∎




  -- The product of ℐ𝓃𝓉 carries over the models : the product of two models is a model
  module _ (M N : Model) where
    open Product.Producted
    open HomReasoning
    open InterpretationCategory
    A×B-ℳ : Model
    A×B-ℳ = record
              { interpretation = A×B-ℐ𝓃𝓉 Σ cartesian-𝒞 (interpretation M) (interpretation N)
              ; is-model = is-model-product M N
              }


  -- The cartesian structure of the category of models

  module _ {M N : Model} where
    import Categories.Object.Product.Core
    open Categories.Object.Product.Core.Product
    open InterpretationCategory Σ cartesian-𝒞
    private
      UM UN : Interpretation
      UM = interpretation M
      UN = interpretation N
      UM×UN : Product ℐ𝓃𝓉 UM UN
      UM×UN = product-ℐ𝓃𝓉
    product-ℳ : Product ℳ M N
    -- Structure
    A×B      product-ℳ = A×B-ℳ M N
    π₁       product-ℳ = π₁    UM×UN
    π₂       product-ℳ = π₂    UM×UN
    ⟨_,_⟩    product-ℳ = ⟨_,_⟩ UM×UN
    -- Properties
    project₁ product-ℳ {O} {h} {i}     = project₁ UM×UN {interpretation O} {h} {i}
    project₂ product-ℳ {O} {h} {i}     = project₂ UM×UN {interpretation O} {h} {i}
    unique   product-ℳ {O} {h} {i} {j} = unique   UM×UN {interpretation O} {h} {i} {j}
