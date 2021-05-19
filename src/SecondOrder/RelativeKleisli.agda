open import Agda.Primitive using (_⊔_)
open import Categories.Category
open import Categories.Functor
open import Categories.Monad.Relative

module SecondOrder.RelativeKleisli
         {o l e o' l' e'}
         {𝒞 : Category o l e}
         {𝒟 : Category o' l' e'}
         {J : Functor 𝒞 𝒟}
         {M : Monad J}
       where

  Kleisli : Category o l' e'
  Kleisli =
    let open Category in
    let open Functor in
    record
      { Obj = Obj 𝒞
      ; _⇒_ = λ A B →  𝒟 [ F₀ J A , Monad.F₀ M B ]
      ; _≈_ = _≈_ 𝒟
      ; id = Monad.unit M
      ; _∘_ = λ f g → _∘_ 𝒟 (Monad.extend M f) g
      -- the following properties should follow quite directly from the corresponding
      -- properties of the relative monad M
      ; assoc = λ {A} {B} {C} {D} {f} {g} {h}
                → Equiv.trans 𝒟 (∘-resp-≈ˡ 𝒟 (Monad.assoc M)) (assoc 𝒟)
      ; sym-assoc = λ {A} {B} {C} {D} {f} {g} {h}
                    → Equiv.sym 𝒟 (Equiv.trans 𝒟 (∘-resp-≈ˡ 𝒟 (Monad.assoc M)) (assoc 𝒟))
      ; identityˡ = λ {A} {B} {f}
                    → Equiv.trans 𝒟 (∘-resp-≈ˡ 𝒟 (Monad.identityˡ M)) (identityˡ 𝒟)
      ; identityʳ = λ {A} {B} {f}
                    → Monad.identityʳ M
      ; identity² = λ {A} → Equiv.trans 𝒟 ((∘-resp-≈ˡ 𝒟 (Monad.identityˡ M))) (identityˡ 𝒟)
      ; equiv = equiv 𝒟
      ; ∘-resp-≈ = λ p₁ p₂ → ∘-resp-≈ 𝒟 (Monad.extend-≈ M p₁) p₂
      }
