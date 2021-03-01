open import Agda.Primitive
open import Agda.Builtin.Nat
open import Data.Fin

open import Categories.Category
open import Categories.Category.Cartesian

open import SingleSorted.AlgebraicTheory
open import SingleSorted.Interpretation

module SingleSorted.Model {ℓt} {Σ : Signature} (T : Theory ℓt Σ)  where

  -- open Category 𝒞
  -- open import Categories.Object.Product 𝒞
  -- open Cartesian cartesian-𝒞
  -- open HomReasoning

  open Signature
  open Theory

  -- Model of a theory
  record Model {o ℓ e} {𝒞 : Category o ℓ e} {cartesian-𝒞 : Cartesian 𝒞}
            (I : Interpretation Σ cartesian-𝒞) : Set (ℓt ⊔ o ⊔ ℓ ⊔ e) where

    open Interpretation I
    open Category 𝒞

    field
      model-eq : ∀ (ε : eq T) → interp-term (eq-lhs T ε) ≈ interp-term (eq-rhs T ε)

  -- Every theory has the trivial model, whose carrier is the terminal object
  TrivialM : ∀ {o ℓ e} {𝒞 : Category o ℓ e} (cartesian-𝒞 : Cartesian 𝒞) → Model (TrivialI Σ cartesian-𝒞)
  TrivialM cart =
     let open Cartesian cart in
     record { model-eq = λ ε → !-unique₂}

  -- The syntactic category
  SyntacticCategory : Category lzero lzero (lsuc ℓt)
  SyntacticCategory =
    let open Theory in
      record
        { Obj = Context
        ; _⇒_ = substitution Σ
        ; _≈_ = _≈s_ T
        ; id =  id-substitution
        ; _∘_ =  _∘s_
        ; assoc = {!!}
        ; sym-assoc = {!!}
        ; identityˡ = {!!}
        ; identityʳ = {!!}
        ; identity² = {!!}
        ; equiv = {!!}
        ; ∘-resp-≈ = {!!}
        }

  -- The cartesian structure of the syntactic category
  cartesian-SyntacticCategory : Cartesian SyntacticCategory
  cartesian-SyntacticCategory = {!!}

  -- The universal interpretation
  universalI : Interpretation Σ cartesian-SyntacticCategory
  universalI = record { interp-carrier = 1
                      ; interp-oper = {!!} }

  -- The universal model
  UniversalM : Model universalI
  UniversalM = record { model-eq = {!!} }
