module SingleSorted.Examples where

open import SingleSorted.Preamble
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_×_; proj₁; proj₂; <_,_>)
import Function using (_∘_)
open import SingleSorted.AlgebraicTheory
open import Categories.Category.Instance.Sets
open import Categories.Category.Cartesian
open import Agda.Primitive
open import Categories.Category

module Sets₀ where
  𝒮 : Category (lsuc lzero) lzero lzero
  𝒮 = Sets lzero

open Sets₀
open Category 𝒮


record singleton : Set where
  constructor ⋆
 
η-singleton : ∀ (x : singleton) → ⋆ ≡ x
η-singleton ⋆ = refl

-- first-factor : ∀ {X A B : Set} {f : X → A} {g : X → B} → proj₁ Function.∘ < f , g > ≡ f
-- first-factor {X} {A} {B} {f} {g} = funext λ{ x → refl}

first-factor :  ∀ {X A B : Obj} {f : X ⇒ A} {g : X ⇒ B} {x : X} → proj₁ ∘ < f , g > ≡ f
first-factor {X} {A} {B} {f} {g} = funext λ x → refl

second-factor : ∀ {X A B : Obj} {f : X ⇒ A} {g : X ⇒ B} → proj₂ ∘ < f , g > ≡ g
second-factor {X} {A} {B} {f} {g} = funext λ{ x → refl}

cartesian-Sets : Cartesian 𝒮
cartesian-Sets = 
  record
    { terminal = record
                 { ⊤ = singleton
                 ; ⊤-is-terminal = record
                                   { ! = λ{ x → ⋆}
                                   ; !-unique = λ{ f {x} → η-singleton (f x)}
                                   }
                 }
    ; products = record
                 { product = λ {A} {B} → 
                           record
                           { A×B = A × B
                           ; π₁ = proj₁
                           ; π₂ = proj₂
                           ; ⟨_,_⟩ = <_,_>
                           ; project₁ = λ{ → refl}
                           ; project₂ = λ{ → refl}
                           ; unique = λ{ → {!!}}
                           }
                 }
    }
