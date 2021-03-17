{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Data.Fin

open import Categories.Category
open import Categories.Category.Cartesian

open import SingleSorted.AlgebraicTheory
open import SingleSorted.FactsAboutCartesianCategories

module SingleSorted.Interpretation
         {o ℓ e}
         (Σ : Signature) {𝒞 : Category o ℓ e}
         (cartesian-𝒞 : Cartesian 𝒞) where
  open Signature
  open Category 𝒞
  open Cartesian cartesian-𝒞
  open HomReasoning


-- I tried to reorganise this file and moved the definitions and lemmas about cartesian categories and powers in another file, but now I have to explicitely say what signature and cartesian  category I use (as in pow-tuple Σ cartesian-𝒞 (λ i → interp-term (ts i)) ) : Is there a way to avoid this ?

  -- An interpretation of Σ in 𝒞
  record Interpretation : Set (o ⊔ ℓ ⊔ e) where

    field
      interp-carrier : Obj
      interp-oper : ∀ (f : oper Σ) → pow Σ cartesian-𝒞 interp-carrier (oper-arity Σ f) ⇒ interp-carrier

    -- the interpretation of a term
    interp-term : ∀ {Γ : Context} → Term {Σ} Γ →  𝒞 [ (pow Σ cartesian-𝒞 interp-carrier Γ) , interp-carrier ]
    interp-term (tm-var x) = pow-π Σ cartesian-𝒞 x
    interp-term (tm-oper f ts) = interp-oper f ∘ pow-tuple Σ cartesian-𝒞 (λ i → interp-term (ts i))


  open Interpretation

  -- Every signature has the trivial interpretation

  TrivialI : Interpretation
  TrivialI = record { interp-carrier = ⊤ ; interp-oper = λ f → ! }

  record HomI (A B : Interpretation) : Set (o ⊔ ℓ ⊔ e) where
    open Interpretation

    field
      hom-morphism : interp-carrier A  ⇒ interp-carrier B
      hom-commute :
         ∀ (f : oper Σ) →
         hom-morphism ∘ interp-oper A f ≈
             interp-oper B f ∘ pow-tuple Σ cartesian-𝒞 {n = oper-arity Σ f} (λ i → hom-morphism ∘ pow-π Σ cartesian-𝒞 i)
  open HomI

  -- The identity homomorphism
  IdI : ∀ (A : Interpretation) → HomI A A
  IdI A = record
          { hom-morphism = id
          ; hom-commute = λ f → identityˡ ○ ((⟺ identityʳ) ○
                                 (refl⟩∘⟨ ⟺ (pow-tuple-id2 Σ cartesian-𝒞 {A = interp-carrier A} {n = oper-arity Σ f} {f = λ i → id ∘ pow-π Σ cartesian-𝒞 i} (λ i → identityˡ))))
          }

  -- Compositon of homomorphisms
  _∘I_ : ∀ {A B C : Interpretation} → HomI B C → HomI A B → HomI A C
  _∘I_ {A} {B} {C} ϕ ψ =
    let open HomI in
    record { hom-morphism = (hom-morphism ϕ) ∘ (hom-morphism ψ)
             ; hom-commute = {!!}
-- First attempt (doesn't work) : assoc ○ (∘-resp-≈ʳ (hom-commute ψ f) ○ (sym-assoc ○ (∘-resp-≈ˡ (hom-commute ϕ f) ○ (assoc ○ ((⟺ (∘-resp-≈ʳ (pow-tuple-∘ {{!!}} {n = oper-arity Σ f} {fs = (λ i → hom-morphism ϕ ∘ pow-π i)} {g = pow-tuple (λ i → hom-morphism ψ ∘ pow-π i)}))) ○ ∘-resp-≈ʳ (pow-tuple-eq {f = λ i → (hom-morphism ϕ ∘ pow-π i) ∘ pow-tuple (λ i₁ → hom-morphism ψ ∘ pow-π i₁)} {g = λ i → (hom-morphism ϕ ∘ hom-morphism ψ) ∘ pow-π i} λ i → assoc {f = pow-tuple (λ i₁ → hom-morphism ψ ∘ pow-π i₁) } {g = pow-π i} {h = hom-morphism ϕ} ○ ⟺ (assoc ○ ∘-resp-≈ʳ (⟺ (pow-tuple-π {i = i})))))))))
           }


-- Here, there is a problem with the way I want to show the following equality : I can not use pow-tuple-∘, maybe because pow-π i depends on i
-- pow-tuple (λ i → (hom-morphism ϕ ∘ hom-morphism ψ) ∘ pow-π i) ≈
-- pow-tuple (λ i → hom-morphism ϕ ∘ pow-π i) ∘
-- pow-tuple (λ i → hom-morphism ψ ∘ pow-π i)
