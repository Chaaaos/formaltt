open import Agda.Primitive using (_⊔_; lsuc)

open import Categories.Category
open import Categories.Functor
import Categories.Category.Cartesian as Cartesian
open import Categories.Monad.Relative

import SecondOrder.RelativeKleisli
open import SecondOrder.RelativeMonadMorphism

-- The category of relative monads and relative monad morphisms

module SecondOrder.RelMon
  {o l e o' l' e'}
  {𝒞 : Category o l e}
  {𝒟 : Category o' l' e'}
  {J : Functor 𝒞 𝒟}
  where

RelMon : Category (o ⊔ o' ⊔ l' ⊔ e') (lsuc o ⊔ lsuc l' ⊔ lsuc e') (o ⊔ e')
RelMon =
  let open Category 𝒟 renaming (id to id_D; identityˡ to identˡ; identityʳ to identʳ; assoc to ass) in
  let open RMonadMorph in
  let open Monad in
  let open HomReasoning in
  record
    { Obj = Monad J
    ; _⇒_ = λ M N → RMonadMorph M N
    ; _≈_ = λ {M} {N} φ ψ → ∀ X → morph φ {X} ≈ morph ψ {X}
    ; id = λ {M} →
           record
           { morph = λ {X} → id_D {F₀ M X}
           ; law-unit = λ {X} → identˡ
           ; law-extend = λ {X} {Y} {f} →
                        begin
                          (id_D ∘ extend M f) ≈⟨ identˡ ⟩
                          extend M f ≈⟨ extend-≈ M {k = f} {h = id_D ∘ f} (⟺ identˡ) ⟩
                          extend M (id_D ∘ f) ≈⟨ ⟺ identʳ ⟩
                          (extend M (id_D ∘ f) ∘ id_D)
                        ∎
           }
    ; _∘_ = λ {M} {N} {L} φ ψ →
          record
          { morph = λ {X} → (morph φ {X}) ∘ (morph ψ {X})
          ; law-unit = λ {X} →
                     begin
                       ((morph φ ∘ morph ψ) ∘ unit M) ≈⟨ ass ⟩
                       (morph φ ∘ (morph ψ ∘ unit M)) ≈⟨ refl⟩∘⟨ law-unit ψ ⟩
                       (morph φ ∘ unit N) ≈⟨ law-unit φ ⟩
                       unit L
                     ∎
          ; law-extend = λ {X} {Y} {f} →
                       begin
                         (morph φ ∘ morph ψ) ∘ extend M f ≈⟨ ass ⟩
                         morph φ ∘ (morph ψ ∘ extend M f) ≈⟨ refl⟩∘⟨ law-extend ψ ⟩
                         morph φ ∘ (extend N (morph ψ ∘ f) ∘ morph ψ) ≈⟨ ⟺ (ass) ⟩
                         (morph φ ∘ extend N (morph ψ ∘ f)) ∘ morph ψ ≈⟨ (law-extend φ  ⟩∘⟨refl) ⟩
                         ((extend L (morph φ ∘ morph ψ ∘ f)) ∘ morph φ) ∘ morph ψ ≈⟨ ass ⟩
                         (extend L (morph φ ∘ morph ψ ∘ f)) ∘ morph φ ∘ morph ψ
                                 ≈⟨ ( extend-≈ L (⟺ (ass)) ⟩∘⟨refl) ⟩
                         extend L ((morph φ ∘ morph ψ) ∘ f) ∘ morph φ ∘ morph ψ
                       ∎
          }
    ; assoc = λ X  → ass
    ; sym-assoc = λ X → ⟺ (ass)
    ; identityˡ = λ X → identˡ
    ; identityʳ = λ X → identʳ
    ; identity² = λ X → identˡ
    ; equiv = record
              { refl = λ X → Equiv.refl
              ; sym = λ φ≈ψ X → ⟺ (φ≈ψ X)
              ; trans = λ φ≈ψ ψ≈θ X → φ≈ψ X ○ ψ≈θ X
              }
    ; ∘-resp-≈ = λ φ≈ψ θ≈ω X → φ≈ψ X ⟩∘⟨ θ≈ω X
    }
