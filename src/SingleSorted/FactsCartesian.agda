{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Nat
open import Data.Fin

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

open import SingleSorted.AlgebraicTheory

module SingleSorted.FactsCartesian
       {o ℓ e}
       {𝒞 : Category.Category o ℓ e}
       (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
  open Category.Category 𝒞
  open Cartesian.Cartesian cartesian-𝒞 public
  open HomReasoning

  -- We use our own definition of powers, because the one in the library has a silly special case n = 1
  pow : ∀ (A : Obj) (n : Nat) → Obj
  pow A zero = ⊤
  pow A (suc n) = pow A n × A

  pow-π : ∀ {A : Obj} {n : Nat} (i : Fin n) → pow A n ⇒ A
  pow-π {_} {suc n} zero = π₂
  pow-π {_} {suc n} (suc i) = (pow-π i) ∘ π₁

  -- We make the argument n explicit because Agda has a hard time telling what it is
  -- by looking at the function.
  pow-tuple : ∀ {A B : Obj} (n : Nat) → (Fin n → A ⇒ B) → A ⇒ pow B n
  pow-tuple zero fs = !
  pow-tuple (suc n) fs = ⟨ (pow-tuple n (λ i → fs (suc i))) , (fs zero) ⟩

  pow-tuple-∘ : ∀ {A B C : Obj} {n : Nat} {fs : Fin n → B ⇒ C} {g : A ⇒ B} →
                pow-tuple n (λ i → fs i ∘ g) ≈ pow-tuple n fs ∘ g
  pow-tuple-∘ {n = zero} {fs} {g} = !-unique (! ∘ g)
  pow-tuple-∘ {n = suc n} {fs = fs} =
    let open product in
      (⟨⟩-congʳ (pow-tuple-∘ {fs = λ i → fs (suc i)})) ○ (⟺ ⟨⟩∘)

  pow-tuple-id : ∀ {A : Obj} {n} → pow-tuple {A = pow A n} n pow-π ≈ id
  pow-tuple-id {n = zero} = !-unique id
  pow-tuple-id {n = suc n} = (⟨⟩-congʳ ((pow-tuple-∘ {n = n}) ○ ((pow-tuple-id {n = n} ⟩∘⟨refl) ○ identityˡ))) ○ η

  pow-tuple-eq :  ∀ {A B : Obj} {n} {f g : Fin n → A ⇒ B} → (∀ i →  f i ≈ g i) →
                  pow-tuple n f ≈ pow-tuple n g
  pow-tuple-eq {n = zero} _ = !-unique₂
  pow-tuple-eq {n = suc n} ξ = ⟨⟩-cong₂ (pow-tuple-eq (λ i → ξ (suc i))) (ξ zero)

  pow-tuple-id2 : ∀ {A : Obj} {n : Nat} {f : Fin n → pow A n ⇒ A} → (∀ i → f i ≈ pow-π i) → pow-tuple n f ≈ id
  pow-tuple-id2 {A} {n} {f} ξ = pow-tuple-eq ξ ○ (pow-tuple-id {A = A} {n = n})

  pow-π-tuple : ∀ {A B : Obj} {n} {fs : Fin n → A ⇒ B} {i : Fin n} →
                (pow-π i ∘ pow-tuple n fs) ≈ fs i
  pow-π-tuple {n = suc n} {i = zero} =  project₂
  pow-π-tuple {A = A} {n = suc (suc n)} {fs} {i = suc i} =
    begin
      pow-π (suc i) ∘ pow-tuple (suc (suc n)) fs             ≈⟨ assoc ⟩
      pow-π i ∘ π₁ ∘ pow-tuple (suc (suc n)) fs              ≈⟨ refl⟩∘⟨ project₁ ⟩
      pow-π i ∘ pow-tuple (suc n) (λ j → fs (suc j))         ≈⟨ pow-π-tuple {fs = λ j → fs (suc j)} {i = i} ⟩
      fs (suc i) ∎
