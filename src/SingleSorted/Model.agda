{-# OPTIONS --allow-unsolved-metas #-}
open import SingleSorted.AlgebraicTheory
open import SingleSorted.Interpretation using (Interpretation; TrivialI)

module SingleSorted.Model {ℓt} {Σ : Signature} (T : Theory ℓt Σ) where

  open import Agda.Builtin.Nat public
  open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
  open import Agda.Builtin.Equality
  open import Data.Fin renaming (_+_ to _+ᶠ_)
  open import Function.Base
  open import Data.Sum.Base
  open import Data.Nat.Properties using (+-comm)
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong-app; trans) renaming (sym to symm)
  open Eq.≡-Reasoning

  open import Categories.Category

  open import Categories.Category.Cartesian

  open import SingleSorted.Interpretation public
  open import SingleSorted.CartesianCategories public
  open import SingleSorted.FiniteSets public

  open Signature Σ
  open Theory T


  -- Model of a theory

  record Model {o ℓ e} {𝒞 : Category o ℓ e} {cartesian-𝒞 : Cartesian 𝒞}
            (I : Interpretation Σ cartesian-𝒞) : Set (ℓt ⊔ o ⊔ ℓ ⊔ e) where

    open Interpretation I
    open Category 𝒞

    field
      model-eq : ∀ (ε : eq) → interp-term (eq-lhs ε) ≈ interp-term (eq-rhs ε)

  -- Every theory has the trivial model, whose carrier is the terminal object
  TrivialM : ∀ {o ℓ e} {𝒞 : Category o ℓ e} (cartesian-𝒞 : Cartesian 𝒞) → Model (TrivialI Σ cartesian-𝒞)
  TrivialM cart =
     let open Cartesian cart in
     record { model-eq = λ ε → !-unique₂ }
