module Category where

open import Agda.Primitive
open import Agda.Builtin.Equality

record Cat ℓ : Set (lsuc ℓ) where
  field
    obj : Set ℓ
    hom : obj → obj → Set ℓ
    id : ∀ {x} → hom x x
    compose : ∀ {x y z} → hom y z → hom x y → hom x z
    compose-id-left : ∀ {x y} (f : hom x y) → compose id f ≡ f
    compose-id-right : ∀ {x y} (f : hom x y) → compose f id ≡ f
    compose-assoc : ∀ {x y z w} {f : hom x y} {g : hom y z} {h : hom z w} → compose (compose h g) f ≡ compose h (compose g f)

open Cat

-- the product of a and b in a category C
record product {ℓ} {C : Cat ℓ} (a b : obj C) : Set ℓ where
  field
    _×_ : obj C
    pr₁ : hom C _×_ a
    pr₂ : hom C _×_ b
    pair : ∀ {c : obj C} (f : hom C c a) (g : hom C c b) → hom C c _×_
    pr₁-pair : ∀ {c : obj C} (f : hom C c a) (g : hom C c b) → compose C pr₁ (pair f g) ≡ f
    pr₂-pair : ∀ {c : obj C} (f : hom C c a) (g : hom C c b) → compose C pr₂ (pair f g) ≡ g
    pair-pr : ∀ {c : obj C} (u : hom C c _×_) → pair (compose C pr₁ u) (compose C pr₂ u) ≡ u
