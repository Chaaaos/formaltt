{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Data.Fin

open import Categories.Category
open import Categories.Category.Cartesian

open import SingleSorted.AlgebraicTheory

module SingleSorted.Interpretation
         {o ℓ e}
         (Σ : Signature) {𝒞 : Category o ℓ e}
         (cartesian-𝒞 : Cartesian 𝒞) where
  open Signature
  open Category 𝒞
  open Cartesian cartesian-𝒞
  open HomReasoning

  -- We use our own definition of powers, because the one in the library has a silly special case n = 1
  pow : ∀ (A : Obj) (n : Nat) → Obj
  pow A zero = ⊤
  pow A (suc n) = pow A n × A

  pow-π : ∀ {A : Obj} {n : Nat} (i : Fin n) → pow A n ⇒ A
  pow-π {_} {suc n} zero = π₂
  pow-π {_} {suc n} (suc i) = (pow-π i) ∘ π₁

  pow-tuple : ∀ {A B : Obj} {n : Nat} → (Fin n → A ⇒ B) → A ⇒ pow B n
  pow-tuple {n = zero} fs = !
  pow-tuple {n = suc n} fs = ⟨ (pow-tuple (λ i → fs (suc i))) , (fs zero) ⟩

  pow-tuple-∘ : ∀ {A B C : Obj} {n : Nat} {fs : Fin n → B ⇒ C} {g : A ⇒ B} →
                pow-tuple (λ i → fs i ∘ g) ≈ pow-tuple fs ∘ g
  pow-tuple-∘ {n = zero} {fs} {g} = !-unique (! ∘ g)
  pow-tuple-∘ {n = suc n} {fs = fs} =
    let open product in
      (⟨⟩-congʳ (pow-tuple-∘ {fs = λ i → fs (suc i)})) ○ (⟺ ⟨⟩∘)

  pow-tuple-id : ∀ {A : Obj} {n} → pow-tuple {A = pow A n} {n = n} pow-π ≈ id
  pow-tuple-id {n = zero} = !-unique id
  pow-tuple-id {n = suc n} = (⟨⟩-congʳ ((pow-tuple-∘ {n = n}) ○ ((pow-tuple-id {n = n} ⟩∘⟨refl) ○ identityˡ))) ○ η

  -- An interpretation of Σ in 𝒞
  record Interpretation : Set (o ⊔ ℓ ⊔ e) where

    field
      interp-carrier : Obj
      interp-oper : ∀ (f : oper Σ) → pow interp-carrier (oper-arity Σ f) ⇒ interp-carrier

    -- the interpretation of a term
    interp-term : ∀ {Γ : Context} → Term {Σ} Γ →  𝒞 [ (pow interp-carrier Γ) , interp-carrier ]
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
         ∀ (f : oper Σ) →
         hom-morphism ∘ interp-oper A f ≈
             interp-oper B f ∘ pow-tuple {n = oper-arity Σ f} (λ i → hom-morphism ∘ pow-π i)

  -- The identity homomorphism
  IdI : ∀ (A : Interpretation) → HomI A A
  IdI A = record
          { hom-morphism = id
          ; hom-commute = λ f → {!!}
          }

  -- Compositon of homomorphisms
  _∘I_ : ∀ {A B C : Interpretation} → HomI B C → HomI A B → HomI A C
  ϕ ∘I ψ =
    let open HomI in
    record { hom-morphism = (hom-morphism ϕ) ∘ (hom-morphism ψ)
           ; hom-commute = {!!} }
