{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid; cong; trans)
import Function.Equality
open import Relation.Binary using (Setoid)

open import Categories.Category
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Monad.Relative
open import Categories.Category.Equivalence
open import Categories.Category.Cocartesian

module SecondOrder.RMonadsMorphism
  {o ℓ e o′ ℓ′ e′ : Level}
  (C : Category o ℓ e)
  (D : Category o′ ℓ′ e′)
  where

  record RMonadMorph {J : Functor C D} (M M’ : Monad J) : Set (lsuc (o ⊔ ℓ′))
    where
      open Category D
      open Monad
      field
        morph : ∀ {X} → (F₀ M X) ⇒ (F₀ M’ X)
        law-unit : ∀ {X} → morph ∘ (unit M {X}) ≡ unit M’ {X}
        law-extend : ∀ {X Y} {k : (Functor.F₀ J X) ⇒ (F₀ M Y)}
                → (morph {Y}) ∘ (extend  M k)
                  ≡ (extend M’ ((morph {Y}) ∘ k)) ∘ (morph {X})
