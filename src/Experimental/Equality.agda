open import Agda.Primitive

module Equality where

  data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
    refl : ∀ {x : A} → x ≡ x

  sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  tran : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  tran refl q = q

  ap : ∀ {ℓ k} {A : Set ℓ} {B : Set k} {x y : A} {f : A → B} → x ≡ y → f x ≡ f y
  ap refl = refl

  transport : ∀ {ℓ k} {A : Set ℓ} (B : A → Set k) {x y : A} → x ≡ y → B x → B y
  transport _ refl u = u
