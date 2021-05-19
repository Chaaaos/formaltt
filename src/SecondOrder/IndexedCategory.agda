open import Agda.Primitive
open import Categories.Category

module SecondOrder.IndexedCategory where

  IndexedCategory : ∀ {i o l e} (I : Set i) (𝒞 : Category o l e) → Category (i ⊔ o) (i ⊔ l) (i ⊔ e)
  IndexedCategory I 𝒞 =
    let open Category 𝒞 in
    record
      { Obj = I → Obj
      ; _⇒_ = λ A B → ∀ i → A i ⇒ B i
      ; _≈_ = λ f g → ∀ i → f i ≈ g i
      ; id = λ i → id
      ; _∘_ = λ f g i → f i ∘ g i
      ; assoc = λ i → assoc
      ; sym-assoc = λ i → sym-assoc
      ; identityˡ = λ i → identityˡ
      ; identityʳ = λ i → identityʳ
      ; identity² = λ i → identity²
      ; equiv = record { refl = λ i → Equiv.refl
                       ; sym = λ ξ i → Equiv.sym (ξ i) ; trans = λ ζ ξ i → Equiv.trans (ζ i) (ξ i) }
      ; ∘-resp-≈ = λ ζ ξ i → ∘-resp-≈ (ζ i) (ξ i)
      }
