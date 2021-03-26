open import Agda.Primitive using (_⊔_; lsuc; lzero)

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

import MultiSorted.Model as Model
import MultiSorted.Interpretation as Interpretation
import MultiSorted.UniversalModel as UniversalModel
import MultiSorted.SyntacticCategory as SyntacticCategory
import MultiSorted.UniversalModel as UniversalModel

open import MultiSorted.AlgebraicTheory

module MultiSorted.Completeness
         {ℓt}
         {Σ : Signature}
         (T : Theory ℓt Σ) where

  open Theory T
  open UniversalModel T

  -- An equation is semantically valid when it holds in all models
  valid : ∀ (ε : Equation Σ) → Set (lsuc (lsuc ℓt))
  valid ε = ∀ {𝒞 : Category.Category lzero lzero (lsuc ℓt)}
              {cartesian-𝒞 : Cartesian.Cartesian 𝒞}
              {I : Interpretation.Interpretation Σ cartesian-𝒞}
              (M : Model.Model T I) → Interpretation.Interpretation.⊨_ I ε

  -- Completeness: semantic validity implies provability
  valid-⊢ : ∀ (ε : Equation Σ) → valid ε → ⊢ ε
  valid-⊢ ε v = universality ε (v 𝒰)
