open import Agda.Primitive

open import Equality

module Quotient where

  is-prop : ∀ {ℓ} (A : Set ℓ) → Set ℓ
  is-prop A = ∀ (x y : A) → x ≡ y

  record is-equivalence {ℓ k} {A : Set ℓ} (E : A → A → Set k) : Set (ℓ ⊔ k) where
    field
      equiv-prop : ∀ {x y} → is-prop (E x y)
      equiv-refl : ∀ {x} → E x x
      equiv-symm : ∀ {x y} → E x y → E y x
      equiv-tran : ∀ {x y z} → E x y → E y z → E x z

  record Equivalence {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
    field
      equiv-relation : A → A → Set ℓ
      equiv-is-equivalence : is-equivalence equiv-relation

  is-set : ∀ {ℓ} (A : Set ℓ) → Set ℓ
  is-set A = ∀ (x y : A) (p q : x ≡ y) → p ≡ q

  record HSet ℓ : Set (lsuc ℓ) where
    field
      hset-type : Set ℓ
      hset-is-set : is-set hset-type

  record Quotient {ℓ} (A : Set ℓ) (E : Equivalence A) : Set (lsuc ℓ) where
    open Equivalence

    field
      quot-type : Set ℓ
      quot-class : ∀ (x : A) → quot-type
      quot-≡ : ∀ {x y : A} → equiv-relation E x y → quot-class x ≡ quot-class y
      quot-is-set : is-set quot-type
      quot-elim :
        ∀ (B : ∀ quot-type → Set ℓ)
          (f : ∀ (x : A) → B (quot-class x)) →
          (∀ (x y : A) {ε : equiv-relation E x y} → transport B (quot-≡ ε) (f x) ≡ f y) →
          ∀ (ξ : quot-type) → B ξ
      quot-compute :
        ∀ (B : ∀ quot-type → Set ℓ)  →
          (f : ∀ (x : A) → B (quot-class x)) →
          (η : ∀ (x y : A) {ε : equiv-relation E x y} → transport B (quot-≡ ε) (f x) ≡ f y) →
          (quot-elim ? quot-class η)
