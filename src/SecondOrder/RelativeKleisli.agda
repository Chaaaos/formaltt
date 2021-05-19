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

  Kleisli : Category o (l ⊔ l') (e ⊔ e')
  Kleisli =
    record
      { Obj = Category.Obj 𝒞
      ; _⇒_ = λ A B →  {!𝒟[J A , M B]!}
      ; _≈_ = {!𝒞.≈!}
      ; id = {! use J.unit!}
      ; _∘_ = {! use J.extend!}
      -- the following properties should follow quite directly from the corresponding
      -- properties of the relative monad M
      ; assoc = {!!}
      ; sym-assoc = {!!}
      ; identityˡ = {!!}
      ; identityʳ = {!!}
      ; identity² = {!!}
      ; equiv = {!!}
      ; ∘-resp-≈ = {!!}
      }
