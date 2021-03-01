module Category where

open import Agda.Primitive

open import Equality
open import Finite

record Category ℓ : Set (lsuc ℓ) where
  field
    obj : Set ℓ
    hom : obj → obj → Set ℓ
    id-hom : ∀ {x} → hom x x
    compose : ∀ {x y z} → hom y z → hom x y → hom x z
    compose-id-left : ∀ {x y} {f : hom x y} → compose id-hom f ≡ f
    compose-id-right : ∀ {x y} {f : hom x y} → compose f id-hom ≡ f
    compose-assoc : ∀ {x y z w} {f : hom x y} {g : hom y z} {h : hom z w} → compose (compose h g) f ≡ compose h (compose g f)

record FPCategory ℓ : Set (lsuc ℓ) where
  open Category

  field
    {{category}} : Category ℓ
    product : ∀ n (xs : Fin n → obj category) → obj category
    project : ∀ n {xs : Fin n → obj category} → ∀ (i : Fin n) → hom category (product n xs) (xs i)
    tuple : ∀ n {xs : Fin n → obj category} {y} → ∀ (f : ∀ i → hom category y (xs i)) → hom category y (product n xs)
    project-tuple : ∀ {n} {xs : Fin n → obj category} {y} {f : ∀ i → hom category y (xs i)} {j} →
                   compose category (project n j) (tuple n f) ≡ f j
    tuple-project : ∀ {n} {xs : Fin n → obj category} {y} {u v : hom category y (product n xs)} →
                   (∀ i → compose category (project n i) u ≡ compose category (project n i) v) → u ≡ v

  tuple-hom : ∀ n {xs ys : Fin n → obj category} (f : ∀ i → hom category (xs i) (ys i)) →
              hom category (product n xs) (product n ys)
  tuple-hom n f = tuple n (λ i → compose category (f i) (project n i))

  power : ℕ → obj category → obj category
  power n x = product n (λ _  → x)

  power-hom : ∀ n {x y : obj category} → hom category x y → hom category (power n x) (power n y)
  power-hom n f = tuple-hom n (λ i → f)

  terminal-obj : obj category
  terminal-obj = product Z (λ ())

  terminal-hom : ∀ {x : obj category} → hom category x terminal-obj
  terminal-hom = tuple Z (λ ())

  terminal-eq : ∀ {x : obj category} {f g : hom category x terminal-obj} → f ≡ g
  terminal-eq {x} {f} {g} = tuple-project λ ()
