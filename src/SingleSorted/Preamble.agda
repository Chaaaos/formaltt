open import SingleSorted.AlgebraicTheory

module SingleSorted.Preamble {ℓt} {Σ : Signature} (T : Theory ℓt Σ) where

  -- Opening a lot of mudules, useful here, but also in other files
  -- (because they are open as "public", we don't have to open them everywhere)

  -- Equality
  open import Agda.Builtin.Equality public
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong-app; trans) renaming (sym to symm) public
  open Eq.≡-Reasoning public
  open import Relation.Binary.PropositionalEquality.Core public
  -- Categories
  open import Categories.Category public
  open import Categories.Category.Cartesian public
  open import Data.Nat.Properties using (+-comm) public
  -- Other
  open import SingleSorted.AlgebraicTheory public
  open import Data.Sum.Base renaming ([_,_] to [_⊎_]) public
  open import Function.Base renaming (_∘_ to _●_; id to idᶠ) public

  -- Postulates and useful general properties
  open Signature Σ
  open Theory T

  postulate
    funext : ∀ {l : Level} {X : Set l} {Y : X → Set l} {f g : ∀ (x : X) → (Y x)} → (∀ (x : X) → ((f x) ≡ (g x))) → (f ≡ g)

  congr : ∀ {l : Level} {X Y : Set l} {f : ∀ (x : X) → Y} {x y : X} → (x ≡ y) → (f x ≡ f y)
  congr refl = refl

  eq-builtin-refl : ∀ {l : Level} {Γ : Context} {x : Term Γ} {y : Term Γ} → (x ≡ y) → (Γ ⊢ x ≈ y)
  eq-builtin-refl refl = eq-refl
