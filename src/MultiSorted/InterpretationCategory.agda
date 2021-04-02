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
  module _ (I J : Interpretation) where
    open Interpretation
    open Product.Producted
    open HomReasoning
    A×B-ℐ𝓃𝓉 : Interpretation
    interp-sort A×B-ℐ𝓃𝓉 A = interp-sort I A × interp-sort J A
    -- Contexts
    -- -- Structure
    prod  (interp-ctx A×B-ℐ𝓃𝓉) Γ = prod (interp-ctx I) Γ × prod (interp-ctx J) Γ
    π (interp-ctx A×B-ℐ𝓃𝓉) x = (π (interp-ctx I) x) ⁂ (π (interp-ctx J) x)
    tuple (interp-ctx A×B-ℐ𝓃𝓉) Γ fs = ⟨ (tuple (interp-ctx I) Γ λ x → π₁ ∘ fs x) , ((tuple (interp-ctx J) Γ λ x → π₂ ∘ fs x)) ⟩
    project (interp-ctx A×B-ℐ𝓃𝓉) {Γ} {B} {x} {fs} =
      begin
      π (interp-ctx A×B-ℐ𝓃𝓉) x ∘
        (tuple (interp-ctx A×B-ℐ𝓃𝓉) Γ fs) ≈⟨ ⁂∘⟨⟩ ⟩
      ⟨ π (interp-ctx I) x ∘ tuple (interp-ctx I) Γ (λ x₁ → π₁ ∘ fs x₁) ,
        π (interp-ctx J) x ∘ tuple (interp-ctx J) Γ (λ x₁ → π₂ ∘ fs x₁) ⟩ ≈⟨ ⟨⟩-congʳ (project (interp-ctx I)) ⟩
      ⟨ π₁ ∘ fs x ,
        π (interp-ctx J) x ∘ tuple (interp-ctx J) Γ (λ x₁ → π₂ ∘ fs x₁) ⟩ ≈⟨ ⟨⟩-congˡ (project (interp-ctx J)) ⟩
      ⟨ π₁ ∘ fs x , π₂ ∘ fs x ⟩ ≈⟨ Product.unique product Equiv.refl Equiv.refl ⟩
      fs x ∎
    unique (interp-ctx A×B-ℐ𝓃𝓉) {Γ} {A} {g} {fs} ps = Product.unique product
                                                 (⟺ (unique (interp-ctx I) λ i → begin
                                                 π (interp-ctx I) i ∘ product.π₁  ∘ fs ≈⟨ sym-assoc ⟩
                                                 (π (interp-ctx I) i ∘ product.π₁) ∘ fs ≈⟨ (Π-nat₁ i ⟩∘⟨refl)  ⟩
                                                 (product.π₁ ∘ (π (interp-ctx A×B-ℐ𝓃𝓉) i)) ∘ fs  ≈⟨ assoc ⟩
                                                 product.π₁ ∘((π (interp-ctx A×B-ℐ𝓃𝓉) i)  ∘ fs) ≈⟨ (refl⟩∘⟨ ps i) ⟩
                                                 product.π₁ ∘ g i ∎))
                                                 (⟺ (unique (interp-ctx J) λ i → begin
                                                 (π (interp-ctx J) i ∘ π₂ ∘ fs) ≈⟨ sym-assoc ⟩
                                                 ((π (interp-ctx J) i ∘ π₂) ∘ fs) ≈⟨ (Π-nat₂ i ⟩∘⟨refl) ⟩
                                                 ((product.π₂ ∘ π (interp-ctx A×B-ℐ𝓃𝓉) i) ∘ fs) ≈⟨ assoc ⟩
                                                 (π₂ ∘ π (interp-ctx A×B-ℐ𝓃𝓉) i ∘ fs) ≈⟨ (refl⟩∘⟨ ps i) ⟩
                                                 (π₂ ∘ g i) ∎))
           where
           Π-nat₁ : {Γ : Context} → (i : var Γ) → π (interp-ctx I) i ∘ product.π₁ ≈ product.π₁ ∘ π (interp-ctx A×B-ℐ𝓃𝓉) i
           Π-nat₁ = λ i → ⟺ project₁

           Π-nat₂ : {Γ : Context} → (i : var Γ) → π (interp-ctx J) i ∘ product.π₂ ≈ product.π₂ ∘ π (interp-ctx A×B-ℐ𝓃𝓉) i
           Π-nat₂ = λ i → ⟺ project₂

    -- Operations
    interp-oper A×B-ℐ𝓃𝓉 = λ f → (interp-oper I f) ⁂ (interp-oper J f)


  module _ (I J : Interpretation) f where
    open Product.Producted
    open Interpretation
    open HomReasoning

    Π-nat₁ : {Γ : Context} → (i : var Γ) → π (interp-ctx I) i ∘ product.π₁ ≈ product.π₁ ∘ π (interp-ctx (A×B-ℐ𝓃𝓉 I J)) i
    Π-nat₁ = λ i → ⟺ project₁

    Π-nat₂ : {Γ : Context} → (i : var Γ) → π (interp-ctx J) i ∘ product.π₂ ≈ product.π₂ ∘ π (interp-ctx (A×B-ℐ𝓃𝓉 I J)) i
    Π-nat₂ = λ i → ⟺ project₂

    π₁-tuple : π₁ ≈ tuple (interp-ctx I) (oper-arity f) (λ i → π₁ ∘ (π (interp-ctx I) i ⁂ π (interp-ctx J) i))
    π₁-tuple = ⟺ (begin
                     tuple (interp-ctx I) (oper-arity f)
                       (λ i → π₁ ∘ (π (interp-ctx I) i ⁂ π (interp-ctx J) i)) ≈⟨ tuple-cong (interp-ctx I) (λ i → π₁∘⁂) ⟩
                     tuple (interp-ctx I) (oper-arity f) (λ x → π (interp-ctx I) x ∘ π₁) ≈⟨ ∘-distribʳ-tuple (interp-ctx I) ⟩
                     (tuple (interp-ctx I) (oper-arity f) (λ x → π (interp-ctx I) x) ∘ π₁) ≈⟨ ∘-resp-≈ˡ (Product.Producted.η (interp-ctx I)) ⟩
                     (id ∘ π₁) ≈⟨ identityˡ ⟩
                     π₁ ∎)

    π₂-tuple : π₂ ≈ tuple (interp-ctx J) (oper-arity f) (λ i → π₂ ∘ (π (interp-ctx I) i ⁂ π (interp-ctx J) i))
    π₂-tuple = ⟺ (begin
                      tuple (interp-ctx J) (oper-arity f)
                        (λ i → π₂ ∘ (π (interp-ctx I) i ⁂ π (interp-ctx J) i)) ≈⟨ tuple-cong (interp-ctx J) (λ i → π₂∘⁂) ⟩
                      tuple (interp-ctx J) (oper-arity f) (λ x → π (interp-ctx J) x ∘ π₂) ≈⟨ ∘-distribʳ-tuple (interp-ctx J) ⟩
                      (tuple (interp-ctx J) (oper-arity f) (λ x → π (interp-ctx J) x) ∘ π₂) ≈⟨ ∘-resp-≈ˡ (Product.Producted.η (interp-ctx J)) ⟩
                      (id ∘ π₂) ≈⟨ identityˡ ⟩
                      π₂ ∎)

  π₁-ℐ𝓃𝓉 : ∀ {I J : Interpretation} → A×B-ℐ𝓃𝓉 I J ⇒I I
  π₁-ℐ𝓃𝓉 {I} {J} =
                   let open HomReasoning in
                   let open Product.Producted in
                   let open Interpretation in
                   record
                     { hom-morphism = Cartesian.Cartesian.π₁ cartesian-𝒞
                     ; hom-commute = λ f → begin
                                             (π₁ ∘ interp-oper (A×B-ℐ𝓃𝓉 I J) f) ≈⟨ π₁∘⁂ ⟩
                                             (interp-oper I f ∘ π₁) ≈⟨ ∘-resp-≈ʳ (π₁-tuple I J f) ⟩
                                             (interp-oper I f ∘
                                               tuple (interp-ctx I) (oper-arity f)
                                               (λ i → π₁ ∘ (π (interp-ctx I) i ⁂ π (interp-ctx J) i))) ∎
                     }

  π₂-ℐ𝓃𝓉 : ∀ {I J : Interpretation} → A×B-ℐ𝓃𝓉 I J ⇒I J
  π₂-ℐ𝓃𝓉 {I} {J} =
                   let open HomReasoning in
                   let open Product.Producted in
                   let open Interpretation in
                   record
                     { hom-morphism = Cartesian.Cartesian.π₂ cartesian-𝒞
                     ; hom-commute = λ f → begin
                                             (π₂ ∘ interp-oper (A×B-ℐ𝓃𝓉 I J) f) ≈⟨ π₂∘⁂ ⟩
                                             (interp-oper J f ∘ π₂) ≈⟨ ∘-resp-≈ʳ (π₂-tuple I J f) ⟩
                                             (interp-oper J f ∘
                                               tuple (interp-ctx J) (oper-arity f)
                                               (λ i → π₂ ∘ (π (interp-ctx I) i ⁂ π (interp-ctx J) i))) ∎
                     }
  module _ (I J K : Interpretation) f (ϕ : I ⇒I J) (ψ : I ⇒I K) where
         open Interpretation
         open HomReasoning
         open Product.Producted

         ⟨⟩-left : interp-oper J f ∘ tuple
                                        (interp-ctx J)
                                        (oper-arity f)
                                        (λ x → π₁ ∘ ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩ ∘ π (interp-ctx I) x) ≈ _⇒I_.hom-morphism ϕ ∘ interp-oper I f
         ⟨⟩-left = begin
                   (interp-oper J f ∘
                     tuple (interp-ctx J) (oper-arity f)
                     (λ x →
                        π₁ ∘
                        ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩ ∘ π (interp-ctx I) x)) ≈⟨ ∘-resp-≈ʳ (tuple-cong (interp-ctx J) λ i → sym-assoc) ⟩
                   (interp-oper J f ∘
                     tuple (interp-ctx J) (oper-arity f)
                     (λ x →
                        (π₁ ∘ ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩) ∘
                        π (interp-ctx I) x)) ≈⟨ ∘-resp-≈ʳ (tuple-cong (interp-ctx J) λ i → ∘-resp-≈ˡ project₁) ⟩
                   (interp-oper J f ∘
                     tuple (interp-ctx J) (oper-arity f)
                     (λ x → _⇒I_.hom-morphism ϕ ∘ π (interp-ctx I) x)) ≈⟨ ⟺ (_⇒I_.hom-commute ϕ f) ⟩
                   (_⇒I_.hom-morphism ϕ ∘ interp-oper I f) ∎

         ⟨⟩-right : interp-oper K f ∘ tuple
                                        (interp-ctx K)
                                        (oper-arity f)
                                        (λ x → π₂ ∘ ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩ ∘ π (interp-ctx I) x) ≈ _⇒I_.hom-morphism ψ ∘ interp-oper I f
         ⟨⟩-right = begin
                   (interp-oper K f ∘
                     tuple (interp-ctx K) (oper-arity f)
                     (λ x →
                        π₂ ∘
                        ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩ ∘ π (interp-ctx I) x)) ≈⟨ ∘-resp-≈ʳ (tuple-cong (interp-ctx K) λ i → sym-assoc) ⟩
                   (interp-oper K f ∘
                     tuple (interp-ctx K) (oper-arity f)
                     (λ x →
                        (π₂ ∘ ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩) ∘
                        π (interp-ctx I) x)) ≈⟨ ∘-resp-≈ʳ (tuple-cong (interp-ctx K) λ i → ∘-resp-≈ˡ project₂) ⟩
                   (interp-oper K f ∘
                     tuple (interp-ctx K) (oper-arity f)
                     (λ x → _⇒I_.hom-morphism ψ ∘ π (interp-ctx I) x)) ≈⟨ ⟺ (_⇒I_.hom-commute ψ f) ⟩
                   (_⇒I_.hom-morphism ψ ∘ interp-oper I f) ∎


  ⟨_,_⟩-ℐ𝓃𝓉 : ∀ {I J K : Interpretation} → I ⇒I J → I ⇒I K → I ⇒I A×B-ℐ𝓃𝓉 J K
  ⟨_,_⟩-ℐ𝓃𝓉 {I} {J} {K} ϕ ψ =
     let open HomReasoning in
     let open Product.Producted in
     let open Interpretation in
     record
       { hom-morphism = λ {A} → ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩
       ; hom-commute = λ f →
                             ⟺ (begin
                                     (interp-oper (A×B-ℐ𝓃𝓉 J K) f ∘
                                       tuple (interp-ctx (A×B-ℐ𝓃𝓉 J K)) (oper-arity f)
                                       (λ i →
                                          ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩ ∘ π (interp-ctx I) i)) ≈⟨ ⁂∘⟨⟩ ⟩
                                     ⟨
                                       interp-oper J f ∘
                                       tuple (interp-ctx J) (oper-arity f)
                                       (λ x →
                                          π₁ ∘
                                          ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩ ∘ π (interp-ctx I) x)
                                       ,
                                       interp-oper K f ∘
                                       tuple (interp-ctx K) (oper-arity f)
                                       (λ x →
                                          π₂ ∘
                                          ⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩ ∘ π (interp-ctx I) x)
                                       ⟩ ≈⟨ ⟨⟩-cong₂ (⟨⟩-left I J K f ϕ ψ) (⟨⟩-right I J K f ϕ ψ) ⟩
                                     product.⟨ _⇒I_.hom-morphism ϕ ∘ interp-oper I f ,
                                       _⇒I_.hom-morphism ψ ∘ interp-oper I f ⟩ ≈˘⟨ ⟨⟩∘ ⟩
                                     (⟨ _⇒I_.hom-morphism ϕ , _⇒I_.hom-morphism ψ ⟩ ∘ interp-oper I f) ∎)
       }

  project₁-ℐ𝓃𝓉 : {I J K : Interpretation} {h : I ⇒I J} {i : I ⇒I K} (A : sort) → π₁ ∘ ⟨ _⇒I_.hom-morphism {I} {J} h {A} , _⇒I_.hom-morphism {I} {K} i ⟩ ≈ _⇒I_.hom-morphism h
  project₁-ℐ𝓃𝓉 A = project₁

  project₂-ℐ𝓃𝓉 : {I J K : Interpretation} {h : I ⇒I J} {i : I ⇒I K} (A : sort) → π₂ ∘ ⟨ _⇒I_.hom-morphism {I} {J} h {A} , _⇒I_.hom-morphism {I} {K} i ⟩ ≈ _⇒I_.hom-morphism i
  project₂-ℐ𝓃𝓉 A = project₂

  unique-ℐ𝓃𝓉 : {I J K : Interpretation}
                 {h : I ⇒I A×B-ℐ𝓃𝓉 J K}
                 {i : I ⇒I J} {j : I ⇒I K} →
                 ((A : sort) → π₁ ∘ _⇒I_.hom-morphism h {A} ≈ _⇒I_.hom-morphism i) →
                 ((A : sort) → π₂ ∘ _⇒I_.hom-morphism h {A} ≈ _⇒I_.hom-morphism j) →
                 (A : sort) →
                   ⟨ _⇒I_.hom-morphism i {A} , _⇒I_.hom-morphism j ⟩ ≈ _⇒I_.hom-morphism h
  unique-ℐ𝓃𝓉 = λ p₁ p₂ A → unique (p₁ A) (p₂ A)

  product-ℐ𝓃𝓉 : ∀ {I J} → Product ℐ𝓃𝓉 I J
  product-ℐ𝓃𝓉 {I} {J} =
    record
      { A×B = A×B-ℐ𝓃𝓉 I J
      ; π₁ = π₁-ℐ𝓃𝓉 {I} {J}
      ; π₂ = π₂-ℐ𝓃𝓉 {I} {J}
      ; ⟨_,_⟩ = ⟨_,_⟩-ℐ𝓃𝓉
      ; project₁ = λ {K} {h} {i} A → project₁-ℐ𝓃𝓉 {K} {I} {J} {h} {i} A
      ; project₂ = λ {K} {h} {i} A → project₂-ℐ𝓃𝓉 {K} {I} {J} {h} {i} A
      ; unique = λ {K} {h} {i} {j} p₁ p₂ A → unique-ℐ𝓃𝓉 {K} {I} {J} {h} {i} {j} p₁ p₂ A
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
