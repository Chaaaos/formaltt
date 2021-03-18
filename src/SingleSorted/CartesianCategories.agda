{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Nat
open import Data.Fin

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

module SingleSorted.CartesianCategories
       {o ℓ e}
       (𝒞 : Category.Category o ℓ e)
       (cartesian-𝒞 : Cartesian.Cartesian 𝒞) where
  open Category.Category 𝒞 public
  open Cartesian.Cartesian cartesian-𝒞 public
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

  pow-tuple-eq :  ∀ {A B : Obj} {n} {f g : Fin n → A ⇒ B} → (∀ i → f i ≈ g i) → (pow-tuple {A = A} {n = n} f) ≈ (pow-tuple {A = A} {n = n} g)
  pow-tuple-eq {n = zero} = λ x → Equiv.refl
  pow-tuple-eq {n = suc n} = λ x → Equiv.trans (⟨⟩-congʳ (pow-tuple-eq (λ i → x (suc i)))) (⟨⟩-congˡ (x zero))

  pow-tuple-id2 : ∀ {A : Obj} {n} {f : Fin n → pow A n ⇒ A} → (∀ i → f i ≈ pow-π i) → pow-tuple {A = pow A n} {n = n} f ≈ id
  pow-tuple-id2 {A = A} {n = n} ξ = pow-tuple-eq ξ ○ (pow-tuple-id {A = A} {n = n})

  pow-tuple-π : ∀ {A B : Obj} {n} {f : Fin n → A ⇒ B} {i : Fin n} → pow-π i ∘ (pow-tuple f) ≈ f i
  pow-tuple-π {n = suc n} {i = zero} = project₂
  pow-tuple-π {n = suc n} {f = f} {i = suc i} =
     begin
       pow-π (suc i) ∘ pow-tuple f            ≈⟨ assoc ⟩
       pow-π i ∘ π₁ ∘ pow-tuple f             ≈⟨ refl⟩∘⟨ project₁ ⟩
       pow-π i ∘ pow-tuple (λ j → f (suc j))  ≈⟨ pow-tuple-π {i = i} ⟩
       f (suc i) ∎

  pow-tuple² :
    ∀ {A B C : Obj} {n} (g : B ⇒ C) (f : A ⇒ B) →
      pow-tuple (λ (i : Fin n) → g ∘ pow-π i) ∘ pow-tuple (λ (i : Fin n) → f ∘ pow-π i) ≈
      pow-tuple (λ (i : Fin n) → (g ∘ f) ∘ pow-π i)
  pow-tuple² g f =
      {!!}

  lower : ∀ {A B : Obj} {n} (f : Fin (suc n) → A ⇒ B) → (Fin n → A ⇒ B)
  lower f = λ i → f (suc i)
