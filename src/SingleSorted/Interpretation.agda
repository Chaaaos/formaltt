{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (_⊔_)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

open import SingleSorted.AlgebraicTheory
import SingleSorted.FactsCartesian

module SingleSorted.Interpretation
         {o ℓ e}
         (Σ : Signature) {𝒞 : Category.Category o ℓ e}
         (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
  open Signature Σ
  open Category.Category 𝒞
  open SingleSorted.FactsCartesian cartesian-𝒞

  -- An interpretation of Σ in 𝒞
  record Interpretation : Set (o ⊔ ℓ ⊔ e) where

    field
      interp-carrier : Obj
      interp-oper : ∀ (f : oper) → pow interp-carrier (oper-arity f) ⇒ interp-carrier

    -- the interpretation of a term
    interp-term : ∀ {Γ : Context} → Term {Σ} Γ →  (pow interp-carrier Γ) ⇒ interp-carrier
    interp-term (tm-var x) = pow-π x
    interp-term (tm-oper f ts) = interp-oper f ∘ pow-tuple (λ i → interp-term (ts i))


  -- Every signature has the trivial interpretation

  TrivialI : Interpretation
  TrivialI = record { interp-carrier = ⊤ ; interp-oper = λ f → ! }

  record HomI (A B : Interpretation) : Set (o ⊔ ℓ ⊔ e) where
    open Interpretation

    field
      hom-morphism : interp-carrier A  ⇒ interp-carrier B
      hom-commute :
         ∀ (f : oper) →
         hom-morphism ∘ interp-oper A f ≈
             interp-oper B f ∘ pow-tuple {n = oper-arity f} (λ i → hom-morphism ∘ pow-π i)

  -- The identity homomorphism
  IdI : ∀ (A : Interpretation) → HomI A A
  IdI A =
    let open Interpretation A in
    let open HomReasoning in
    record
      { hom-morphism = id
      ; hom-commute =
         λ f →
          begin
            (id ∘ interp-oper f)       ≈⟨ identityˡ ⟩
            interp-oper f             ≈˘⟨ identityʳ ⟩
            (interp-oper f ∘ id)      ≈˘⟨ (refl⟩∘⟨ pow-tuple-id2 {n = oper-arity f} λ i → identityˡ) ⟩
            (interp-oper f ∘ pow-tuple {n = oper-arity f} (λ i → id ∘ pow-π i)) ∎

      }

  -- Compositon of homomorphisms
  _∘I_ : ∀ {A B C : Interpretation} → HomI B C → HomI A B → HomI A C
  _∘I_ {A} {B} {C} ϕ ψ =
    let open HomI in
    record
      { hom-morphism = (hom-morphism ϕ) ∘ (hom-morphism ψ)
      ; hom-commute =
          let open Interpretation in
          let open HomReasoning in
          λ f → let n = oper-arity f in
            begin
              ((hom-morphism ϕ ∘ hom-morphism ψ) ∘ interp-oper A f)
            ≈⟨ assoc ⟩
              (hom-morphism ϕ ∘ hom-morphism ψ ∘ interp-oper A f)
            ≈⟨ refl⟩∘⟨ hom-commute ψ f ⟩
              (hom-morphism ϕ ∘ interp-oper B f ∘ pow-tuple {n = n} (λ i → hom-morphism ψ ∘ pow-π i))
            ≈˘⟨  assoc ⟩
              ((hom-morphism ϕ ∘ interp-oper B f) ∘ pow-tuple {n = n} (λ i → hom-morphism ψ ∘ pow-π i))
            ≈⟨  hom-commute ϕ f ⟩∘⟨refl ⟩
              (interp-oper C f ∘
               pow-tuple {n = n} (λ i → hom-morphism ϕ ∘ pow-π i)) ∘
               pow-tuple {n = n} (λ i → hom-morphism ψ ∘ pow-π i)
            ≈⟨ assoc ⟩
              (interp-oper C f ∘
               pow-tuple {n = n} (λ i → hom-morphism ϕ ∘ pow-π i) ∘
               pow-tuple {n = n} (λ i → hom-morphism ψ ∘ pow-π i))
            ≈⟨ refl⟩∘⟨ {!pow-tuple²!} ⟩
              {!!}
      }

-- Here, there is a problem with the way I want to show the following equality : I can not use pow-tuple-∘, maybe because pow-π i depends on i
-- pow-tuple (λ i → (hom-morphism ϕ ∘ hom-morphism ψ) ∘ pow-π i) ≈
-- pow-tuple (λ i → hom-morphism ϕ ∘ pow-π i) ∘
-- pow-tuple (λ i → hom-morphism ψ ∘ pow-π i)
