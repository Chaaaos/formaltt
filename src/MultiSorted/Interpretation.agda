open import Agda.Primitive using (_⊔_)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

open import MultiSorted.AlgebraicTheory
import MultiSorted.Product as Product

module MultiSorted.Interpretation
         {o ℓ e}
         (Σ : Signature)
         {𝒞 : Category.Category o ℓ e}
         (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
  open Signature Σ
  open Category.Category 𝒞

  -- An interpretation of Σ in 𝒞
  record Interpretation : Set (o ⊔ ℓ ⊔ e) where

    field
      interp-sort : sort → Obj
      interp-ctx : Product.Producted 𝒞 {Σ = Σ} interp-sort
      interp-oper : ∀ (f : oper) → Product.Producted.prod interp-ctx (oper-arity f) ⇒ interp-sort (oper-sort f)

    open Product.Producted interp-ctx

    -- the interpretation of a term
    interp-term : ∀ {Γ : Context} {A} → Term Γ A → prod Γ ⇒ interp-sort A
    interp-term (tm-var x) = π x
    interp-term (tm-oper f ts) = interp-oper f ∘ tuple (oper-arity f) (λ i → interp-term (ts i))

    -- the interpretation of a substitution
    interp-subst : ∀ {Γ Δ} → Γ ⇒s Δ → prod Γ ⇒ prod Δ
    interp-subst {Γ} {Δ} σ = tuple Δ λ i → interp-term (σ i)

    -- interpretation commutes with substitution
    open HomReasoning

    interp-[]s : ∀ {Γ Δ} {A} {t : Term Δ A} {σ : Γ ⇒s Δ} →
                 interp-term (t [ σ ]s) ≈ interp-term t ∘ interp-subst σ
    interp-[]s {Γ} {Δ} {A} {tm-var x} {σ} = ⟺ (project {Γ = Δ})
    interp-[]s {Γ} {Δ} {A} {tm-oper f ts} {σ} = (∘-resp-≈ʳ
                                                (tuple-cong
                                                  {fs = λ i → interp-term (ts i [ σ ]s)}
                                                  {gs = λ z → interp-term (ts z) ∘ interp-subst σ}
                                                  (λ i → interp-[]s {t = ts i} {σ = σ})
                                              ○ (∘-distribʳ-tuple
                                                  {Γ = oper-arity f}
                                                  {fs = λ z → interp-term (ts z)}
                                                  {g = interp-subst σ})))
                                                ○ (Equiv.refl ○ sym-assoc)

  -- -- Every signature has the trivial interpretation

  open Product 𝒞

  Trivial : Interpretation
  Trivial =
    let open Cartesian.Cartesian cartesian-𝒞 in
    record
      { interp-sort = (λ _ → ⊤)
      ; interp-ctx = StandardProducted (λ _ → ⊤) cartesian-𝒞
      ; interp-oper = λ f → ! }

  record HomI (I J : Interpretation) : Set (o ⊔ ℓ ⊔ e) where
    open Interpretation
    open Producted

    field
      hom-morphism : ∀ {A} → interp-sort I A ⇒ interp-sort J A
      hom-commute :
         ∀ (f : oper) →
         hom-morphism ∘ interp-oper I f ≈
             interp-oper J f ∘ tuple (interp-ctx J) (oper-arity f) (λ i → hom-morphism ∘ π (interp-ctx I) i)

  -- The identity homomorphism
  IdI : ∀ (A : Interpretation) → HomI A A
  IdI A =
    let open Interpretation A in
    let open HomReasoning in
    let open Producted interp-sort in
    record
      { hom-morphism = id
      ; hom-commute = λ f →
                        begin
                          (id ∘ interp-oper f) ≈⟨ identityˡ ⟩
                          interp-oper f       ≈˘⟨ identityʳ ⟩
                          (interp-oper f ∘ id)      ≈˘⟨ refl⟩∘⟨ unique interp-ctx (λ i → identityʳ ○  ⟺ identityˡ) ⟩
                          (interp-oper f ∘
                            Product.Producted.tuple interp-ctx (oper-arity f)
                            (λ i → id ∘ Product.Producted.π interp-ctx i)) ∎
      }

  -- Compositon of homomorphisms
  _∘I_ : ∀ {A B C : Interpretation} → HomI B C → HomI A B → HomI A C
  _∘I_ {A} {B} {C} ϕ ψ =
     let open HomI in
     record { hom-morphism = hom-morphism ϕ ∘ hom-morphism ψ
            ; hom-commute =
                let open Interpretation in
                let open Producted in
                let open HomReasoning in
                λ f →
                  begin
                    (((hom-morphism ϕ) ∘ hom-morphism ψ) ∘ interp-oper A f) ≈⟨ assoc ⟩
                    (hom-morphism ϕ ∘ hom-morphism ψ ∘ interp-oper A f) ≈⟨ (refl⟩∘⟨ hom-commute ψ f) ⟩
                    (hom-morphism ϕ ∘
                      interp-oper B f ∘
                      tuple (interp-ctx B) (oper-arity f)
                      (λ i → hom-morphism ψ ∘ π (interp-ctx A) i)) ≈˘⟨ assoc ⟩
                    ((hom-morphism ϕ ∘ interp-oper B f) ∘
                      tuple (interp-ctx B) (oper-arity f)
                      (λ i → hom-morphism ψ ∘ π (interp-ctx A) i)) ≈⟨ (hom-commute ϕ f ⟩∘⟨refl) ⟩
                     ((interp-oper C f ∘
                       tuple (interp-ctx C) (oper-arity f)
                       (λ i → hom-morphism ϕ ∘ π (interp-ctx B) i))
                      ∘
                      tuple (interp-ctx B) (oper-arity f)
                      (λ i → hom-morphism ψ ∘ π (interp-ctx A) i)) ≈⟨ assoc ⟩
                    (interp-oper C f ∘
                      tuple (interp-ctx C) (oper-arity f)
                      (λ i → hom-morphism ϕ ∘ π (interp-ctx B) i)
                      ∘
                      tuple (interp-ctx B) (oper-arity f)
                      (λ i → hom-morphism ψ ∘ π (interp-ctx A) i)) ≈⟨ (refl⟩∘⟨ ⟺ (∘-distribʳ-tuple (interp-sort C) (interp-ctx C))) ⟩
                    (interp-oper C f ∘
                      tuple (interp-ctx C) (oper-arity f)
                      (λ x →
                         (hom-morphism ϕ ∘ π (interp-ctx B) x) ∘
                         tuple (interp-ctx B) (oper-arity f)
                         (λ i → hom-morphism ψ ∘ π (interp-ctx A) i))) ≈⟨ (refl⟩∘⟨ tuple-cong (interp-sort C) (interp-ctx C) λ i → assoc) ⟩
                    (interp-oper C f ∘
                      tuple (interp-ctx C) (oper-arity f)
                      (λ z →
                         hom-morphism ϕ ∘
                         π (interp-ctx B) z ∘
                         tuple (interp-ctx B) (oper-arity f)
                         (λ i → hom-morphism ψ ∘ π (interp-ctx A) i))) ≈⟨ (refl⟩∘⟨ tuple-cong (interp-sort C) (interp-ctx C) λ i → refl⟩∘⟨ project (interp-ctx B)) ⟩
                    (interp-oper C f ∘
                      tuple (interp-ctx C) (oper-arity f)
                      (λ z → hom-morphism ϕ ∘ hom-morphism ψ ∘ π (interp-ctx A) z)) ≈⟨ (refl⟩∘⟨ tuple-cong (interp-sort C) (interp-ctx C) λ i → sym-assoc) ⟩
                   (interp-oper C f ∘
                     tuple (interp-ctx C) (oper-arity f)
                     (λ z → (hom-morphism ϕ ∘ hom-morphism ψ) ∘ π (interp-ctx A) z)) ∎}
