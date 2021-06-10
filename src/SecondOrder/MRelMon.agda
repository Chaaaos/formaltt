-- {-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; setoid)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; zip; map; <_,_>; swap)
import Function.Equality
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

import Categories.Category
import Categories.Functor
import Categories.Category.Instance.Setoids
import Categories.Monad.Relative
import Categories.Category.Equivalence
import Categories.Category.Cocartesian
import Categories.Category.Construction.Functors
import Categories.Category.Product
import Categories.NaturalTransformation
import Categories.NaturalTransformation.NaturalIsomorphism

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.VRenaming
import SecondOrder.MRenaming
import SecondOrder.Term
import SecondOrder.Substitution
import SecondOrder.RMonadsMorphism
-- import SecondOrder.Instantiation
import SecondOrder.IndexedCategory
import SecondOrder.RelativeKleisli


module SecondOrder.MRelMon
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ
  open SecondOrder.VRenaming Σ
  open SecondOrder.MRenaming Σ
  -- open SecondOrder.Substitution Σ
  -- open import SecondOrder.RMonadsMorphism
  -- open SecondOrder.Instantiation 
  open Categories.Category
  open Categories.Functor using (Functor)
  open Categories.NaturalTransformation renaming (id to idNt)
  open Categories.NaturalTransformation.NaturalIsomorphism renaming (refl to reflNt; sym to symNt; trans to transNt)
  open Categories.Category.Construction.Functors
  open Categories.Category.Instance.Setoids
  open Categories.Category.Product
  -- open Categories.Monad.Relative
  open Function.Equality using () renaming (setoid to Π-setoid)
  open import SecondOrder.IndexedCategory
  -- open import SecondOrder.RelativeKleisli

  MTele = MContexts
  VTele = VContexts


  -- the codomain category of the MSlots functor. It should be equivalent to the
  -- functor category [ MTele x VTele , < Setoid >ₛₒᵣₜ ]
  -- objects are functors, which are really pairs of functions, one on objects
  -- one on morphisms
  -- morphisms in this category are natural transformations
  MCodom : ∀ {Θ : MContext} {A : sort} → Category (lsuc ℓ) ℓ ℓ
  MCodom {Θ} {A} = record
                 { Obj = Functor (Product MTele VTele) (Setoids ℓ ℓ)
                 ; _⇒_ = NaturalTransformation
                 ; _≈_ = {!!}
                 ; id = {!!}
                 ; _∘_ = {!!}
                 ; assoc = {!!}
                 ; sym-assoc = {!!}
                 ; identityˡ = {!!}
                 ; identityʳ = {!!}
                 ; identity² = {!!}
                 ; equiv = {!!}
                 ; ∘-resp-≈ = {!!}
                 }

  module _ where
    open Category
    open NaturalTransformation
    open Function.Equality renaming (_∘_ to _∙_)
    
    ∘ᵥ-resp-≈ : ∀ {o l e o' l' e'} {𝒞 : Category o l e} {𝒟 : Category o' l' e'}
                {F G H : Functor 𝒞 𝒟} {α β : NaturalTransformation F G} {γ δ : NaturalTransformation G H}
              → (∀ {X : Obj 𝒞} → (𝒟 Category.≈ (η α X)) (η β X))
              → (∀ {X : Obj 𝒞} → (𝒟 Category.≈ (η γ X)) (η δ X))
              -------------------------------------------------------------------
              → (∀ {X : Obj 𝒞} → (𝒟 Category.≈ (η (γ ∘ᵥ α) X)) (η (δ ∘ᵥ β) X))
    ∘ᵥ-resp-≈ {𝒟 = 𝒟} α≈β γ≈δ {X = X} = ∘-resp-≈ 𝒟 γ≈δ α≈β

    ∘ᵥ-resp-≈ʳ : ∀ {l o e} {𝒞 𝒟 : Category o l e} {F G H : Functor 𝒞 𝒟} {α : NaturalTransformation G H}
              {β γ : NaturalTransformation F G} → (∀ {X : Obj 𝒞}
                → (𝒟 Category.≈ (η β X)) (η γ X))
              → (∀ {X : Obj 𝒞}
                → (𝒟 Category.≈ (η (α ∘ᵥ β) X)) (η (α ∘ᵥ γ) X))
    ∘ᵥ-resp-≈ʳ {𝒟 = 𝒟} β≈γ {X = X} = ∘-resp-≈ʳ 𝒟 β≈γ
        
    ∘ᵥ-resp-≈ˡ : ∀ {l o e} {𝒞 𝒟 : Category o l e} {F G H : Functor 𝒞 𝒟} {α β : NaturalTransformation G H}
              {γ : NaturalTransformation F G} → (∀ {X : Obj 𝒞}
                → (𝒟 Category.≈ (η α X)) (η β X))
              → (∀ {X : Obj 𝒞}
                → (𝒟 Category.≈ (η (α ∘ᵥ γ) X)) (η (β ∘ᵥ γ) X))
    ∘ᵥ-resp-≈ˡ {𝒟 = 𝒟} α≈β {X = X} = ∘-resp-≈ˡ 𝒟 α≈β


    setoid-resp-≡ : ∀ {c l c' l' c'' l''} {A : Setoid c l} {B : Setoid c' l'} {C : Setoid c'' l''} {f g : A ⟶ B} {h k : B ⟶ C} → f ≡ g → h ≡ k → h ∙ f ≡ k ∙ g
    setoid-resp-≡ eq1 eq2 = {!!}


--   MCodom' : Category (lsuc ℓ) ℓ ℓ
--   MCodom' =
--     let open Category in
--     let open NaturalTransformation in
--     let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
--     let open Relation.Binary.PropositionalEquality.≡-Reasoning in
-- --     let open ≡-Reasoning in 
--     record
--     { Obj = Functor MTele (Functors VTele (Setoids ℓ ℓ))
--     ; _⇒_ = NaturalTransformation
--     ; _≈_ = λ {F} {G} α β
--           → (∀ (ψ : Obj MTele) (Γ : Obj VTele)
--           → η (η α ψ) Γ ≡ η (η β ψ) Γ) -- this might not be the correct equality to use
--     ; id = idNt
--     ; _∘_ = _∘ᵥ_
--     ; assoc = λ ψ Γ → refl
--     ; sym-assoc = λ ψ Γ → refl
--     ; identityˡ = λ ψ Γ → refl
--     ; identityʳ = λ ψ Γ → refl
--     ; identity² = λ ψ Γ → refl
--     ; equiv = record
--               { refl = λ ψ Γ → refl 
--               ; sym = λ α≡β ψ Γ → sym (α≡β ψ Γ) 
--               ; trans = λ α≡β β≡γ ψ Γ → trans (α≡β ψ Γ) (β≡γ ψ Γ)
--               }
--     ; ∘-resp-≈ = λ {F} {G} {H} {α} {β} {γ} {δ} α≡β γ≡δ ψ Γ → setoid-resp-≡ (γ≡δ ψ Γ) (α≡β ψ Γ)
--     }

  MCodom' : Category (lsuc ℓ) ℓ ℓ
  MCodom' =
    let open Category in
    let open Functor in
    let open NaturalTransformation in
    let open Function.Equality using (_⟨$⟩_) renaming (cong to func-cong) in
    let open Category.HomReasoning in
    -- let open Relation.Binary.PropositionalEquality.≡-Reasoning in
    -- let open ≡-Reasoning in 
    record
    { Obj = Functor MTele (Functors VTele (Setoids ℓ ℓ))
    ; _⇒_ = NaturalTransformation
    ; _≈_ = λ {F} {G} α β → ∀ (ψ : Obj MTele) (Γ : Obj VTele)
          → (Setoids ℓ ℓ Category.≈ (η ((η α) ψ) Γ)) (η ((η β) ψ) Γ) 
    ; id = idNt
    ; _∘_ = _∘ᵥ_
    ; assoc = λ ψ Γ x≈y → func-cong (record { _⟨$⟩_ = λ x → x ; cong = λ x → x }) x≈y
    ; sym-assoc = λ ψ Γ x≈y → func-cong (record { _⟨$⟩_ = λ x → x ; cong = λ x → x }) x≈y
    ; identityˡ = λ {F} {G} {α} ψ Γ x≈y → {!F₀ ((F₀ F) ψ) Γ!}
    ; identityʳ = λ ψ Γ x → Setoid.refl {!!}
    ; identity² = Setoid.refl {!!}
    ; equiv = record
              { refl = Setoid.refl {!!}
              ; sym = Setoid.sym {!!}
              ; trans = Setoid.trans {!!}
              }
    ; ∘-resp-≈ = λ α≈β γ≈δ ψ Γ → ∘ᵥ-resp-≈ α≈β γ≈δ
    } 


  Mslots : Functor MContexts (IndexedCategory sort (Functors (Product MTele VTele) (Setoids ℓ ℓ)))
  Mslots = record
            { F₀ = λ Θ A → {!!}
            ; F₁ = {!!}
            ; identity = {!!}
            ; homomorphism = {!!}
            ; F-resp-≈ = {!!}
            }

  Mslots' : Functor MContexts (IndexedCategory sort (MCodom'))
  Mslots' =
    let open Categories.NaturalTransformation in
    let open NaturalTransformation in
          record
            { F₀ = λ Θ A →
                 record
                 { F₀ = λ ψ → Term-Functor {Θ ,, ψ} {A}
                 ; F₁ = λ ι → MRenaming-NT (ᵐʳ⇑ᵐʳ ι)
                 ; identity = λ t≈s → ≈-trans (≈-trans ([]ᵐʳ-resp-≡ᵐʳ ᵐʳ⇑ᵐʳid≡ᵐʳidᵐʳ) [id]ᵐʳ) t≈s
                 ; homomorphism = λ t≈s → ≈-trans ([]ᵐʳ-resp-≈ t≈s) (≈-trans ([]ᵐʳ-resp-≡ᵐʳ ᵐʳ⇑ᵐʳ-∘ᵐʳ) [∘]ᵐʳ)
                 ; F-resp-≈ = λ ι≡μ t≈s → ≈-trans ([]ᵐʳ-resp-≈ t≈s) ([]ᵐʳ-resp-≡ᵐʳ (ᵐʳ⇑ᵐʳ-resp-≡ᵐʳ ι≡μ))
                 }
            ; F₁ = λ {Θ} {Θ'} ι A →
                 record
                 { η = λ Ψ →
                     record { η = λ Γ → η (MRenaming-NT (⇑ᵐʳ ι)) Γ
                            ; commute = commute (MRenaming-NT (⇑ᵐʳ ι))
                            ; sym-commute = sym-commute (MRenaming-NT (⇑ᵐʳ ι))
                            }
                 ; commute = λ {Ψ} {Ξ} ι {Γ} {t} {s} t≈s
                           → ≈-trans ([]ᵐʳ-resp-≈ ([]ᵐʳ-resp-≈ t≈s)) (≈-sym {!split-sum-terms!})
                 ; sym-commute = {!!}
                 }
            ; identity = λ Θ ψ Γ t≈s
              → ≈-trans ([]ᵐʳ-resp-≈ t≈s) (≈-trans ([]ᵐʳ-resp-≡ᵐʳ ⇑ᵐʳid≡ᵐʳidᵐʳ) [id]ᵐʳ)
            ; homomorphism = λ A ψ Γ t≈s
              → ≈-trans ([]ᵐʳ-resp-≈ t≈s) (≈-trans {!!} {!!})
            ; F-resp-≈ = λ ι≡μ A ψ Γ t≈s → ≈-trans ([]ᵐʳ-resp-≈ t≈s) ([]ᵐʳ-resp-≡ᵐʳ (⇑ᵐʳ-resp-≡ᵐʳ ι≡μ))
            }
