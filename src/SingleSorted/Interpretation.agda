{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (_⊔_)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

open import SingleSorted.AlgebraicTheory
import SingleSorted.Power as Power

module SingleSorted.Interpretation
         {o ℓ e}
         (Σ : Signature)
         (𝒞 : Category.Category o ℓ e)
         (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
  open Signature Σ
  open Category.Category 𝒞
  open Power 𝒞

  -- An interpretation of Σ in 𝒞
  record Interpretation : Set (o ⊔ ℓ ⊔ e) where

    field
      interp-carrier : Obj
      interp-power :  Powered interp-carrier
      interp-oper : ∀ (f : oper) → Powered.pow interp-power (oper-arity f) ⇒ interp-carrier

    open Powered interp-power

    -- the interpretation of a term
    interp-term : ∀ {Γ : Context} → Term {Σ} Γ → (pow Γ) ⇒ interp-carrier
    interp-term (tm-var x) = π x
    interp-term (tm-oper f ts) = interp-oper f ∘ tuple (oper-arity f) (λ i → interp-term (ts i))

    -- the interpretation of a context
    interp-ctx : Context → Obj
    interp-ctx Γ = pow Γ

    -- the interpretation of a substitution
    interp-subst : ∀ {Γ Δ} → substitution Σ Γ Δ → interp-ctx Γ ⇒ interp-ctx Δ
    interp-subst {Γ} {Δ} σ = tuple Δ λ i → interp-term (σ i)

    -- interpretation commutes with substitution
    open HomReasoning

    interp-[]s : ∀ {Γ Δ} (t : Term Δ) (σ : substitution Σ Γ Δ) →
                 interp-term (t [ σ ]s) ≈ interp-term t ∘ interp-subst σ
    interp-[]s {Γ} {Δ} (tm-var x) σ = ⟺ (project {Γ = Δ})
    interp-[]s {Γ} {Δ} (tm-oper f ts) σ = (∘-resp-≈ʳ
                                            (tuple-cong
                                              {fs = λ i → interp-term (ts i [ σ ]s)}
                                              {gs = λ z → interp-term (ts z) ∘ interp-subst σ}
                                              (λ i → interp-[]s (ts i) σ)
                                          ○ (∘-distribʳ-tuple
                                              {Γ = oper-arity f}
                                              {ts = λ z → interp-term (ts z)}
                                              {g = interp-subst σ})))
                                            ○ (Equiv.refl ○ sym-assoc)

  -- -- Every signature has the trivial interpretation

  Trivial : Interpretation
  Trivial =
    let open Cartesian.Cartesian cartesian-𝒞 in
    record
      { interp-carrier = ⊤
      ; interp-power = record { pow = λ Γ → ⊤ ; π = {!!} ; tuple = {!!} ; project = {!!} ; unique = {!!} }
      ; interp-oper = {!!} }

  -- record HomI (A B : Interpretation) : Set (o ⊔ ℓ ⊔ e) where
  --   open Interpretation

  --   field
  --     hom-morphism : interp-carrier A  ⇒ interp-carrier B
  --     hom-commute :
  --        ∀ (f : oper) →
  --        hom-morphism ∘ interp-oper A f ≈
  --            interp-oper B f ∘ pow-tuple (oper-arity f) (λ i → hom-morphism ∘ pow-π i)

  -- -- The identity homomorphism
  -- IdI : ∀ (A : Interpretation) → HomI A A
  -- IdI A =
  --   let open Interpretation A in
  --   let open HomReasoning in
  --   record
  --     { hom-morphism = id
  --     ; hom-commute =
  --        λ f →
  --         begin
  --           (id ∘ interp-oper f)       ≈⟨ identityˡ ⟩
  --           interp-oper f             ≈˘⟨ identityʳ ⟩
  --           (interp-oper f ∘ id)      ≈˘⟨ (refl⟩∘⟨ pow-tuple-id2 {Γ = oper-arity f} λ i → identityˡ) ⟩
  --           (interp-oper f ∘ pow-tuple (oper-arity f) (λ i → id ∘ pow-π i)) ∎

  --     }

  -- -- Compositon of homomorphisms
  -- _∘I_ : ∀ {A B C : Interpretation} → HomI B C → HomI A B → HomI A C
  -- _∘I_ {A} {B} {C} ϕ ψ =
  --   let open HomI in
  --   record
  --     { hom-morphism = (hom-morphism ϕ) ∘ (hom-morphism ψ)
  --     ; hom-commute =
  --         let open Interpretation in
  --         let open HomReasoning in
  --         λ f → let n = oper-arity f in
  --           begin
  --             ((hom-morphism ϕ ∘ hom-morphism ψ) ∘ interp-oper A f)
  --           ≈⟨ assoc ⟩
  --             (hom-morphism ϕ ∘ hom-morphism ψ ∘ interp-oper A f)
  --           ≈⟨ refl⟩∘⟨ hom-commute ψ f ⟩
  --             (hom-morphism ϕ ∘ interp-oper B f ∘ pow-tuple n (λ i → hom-morphism ψ ∘ pow-π i))
  --           ≈˘⟨  assoc ⟩
  --             ((hom-morphism ϕ ∘ interp-oper B f) ∘ pow-tuple n (λ i → hom-morphism ψ ∘ pow-π i))
  --           ≈⟨  hom-commute ϕ f ⟩∘⟨refl ⟩
  --             (interp-oper C f ∘
  --              pow-tuple n (λ i → hom-morphism ϕ ∘ pow-π i)) ∘
  --              pow-tuple n (λ i → hom-morphism ψ ∘ pow-π i)
  --           ≈⟨ assoc ⟩
  --             (interp-oper C f ∘
  --              pow-tuple n (λ i → hom-morphism ϕ ∘ pow-π i) ∘
  --              pow-tuple n (λ i → hom-morphism ψ ∘ pow-π i))
  --           ≈⟨ (refl⟩∘⟨ Equiv.sym (pow-tuple-∘ {Γ = oper-arity f} {fs = λ i → hom-morphism ϕ ∘ pow-π i} {g = pow-tuple (oper-arity f) (λ i → hom-morphism ψ ∘ pow-π i)})) ⟩
  --             {!!}
  --     }
