open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)

import Categories.Category
import Categories.Functor
import Categories.Category.Instance.Setoids
import Categories.Category.Cocartesian
import Categories.Monad.Relative

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.Term

module SecondOrder.Renaming
  {ℓs ℓo}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸)
  where

  open SecondOrder.Signature.Signature Σ
  open SecondOrder.Metavariable Σ
  open SecondOrder.Term Σ

  -- a renaming maps variables between contexts in a type-preserving way
  _⇒ʳ_ : ∀ (Γ Δ : Context) → Set ℓs
  Γ ⇒ʳ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

  infix 4 _⇒ʳ_

  -- equality of renamings

  _≡ʳ_ : ∀ {Γ Δ} (σ τ : Γ ⇒ʳ Δ) → Set ℓs
  _≡ʳ_ {Γ} σ τ = ∀ {A} (x : A ∈ Γ) → σ x ≡ τ x

  infixl 3 _≡ʳ_

  ≡ʳ-refl : ∀ {Γ Δ} {ρ : Γ ⇒ʳ Δ} → ρ ≡ʳ ρ
  ≡ʳ-refl = λ x → refl

  ≡ʳ-sym : ∀ {Γ Δ} {ρ ν : Γ ⇒ʳ Δ}
          → ρ ≡ʳ ν
          → ν ≡ʳ ρ
  ≡ʳ-sym eq x = sym (eq x)

  ≡ʳ-trans : ∀ {Γ Δ} {ρ ν γ : Γ ⇒ʳ Δ}
           → ρ ≡ʳ ν
           → ν ≡ʳ γ
           → ρ ≡ʳ γ
  ≡ʳ-trans eq1 eq2 x = trans (eq1 x) (eq2 x)

  -- renamings form a setoid
  renaming-setoid : ∀ (Γ Δ : Context) → Setoid ℓs ℓs
  renaming-setoid Γ Δ =
    record
      { Carrier = Γ ⇒ʳ Δ
      ;  _≈_ = λ ρ ν → ρ ≡ʳ ν
      ; isEquivalence =
                      record
                        { refl = λ {ρ} x → ≡ʳ-refl {Γ} {Δ} {ρ} x
                        ; sym = ≡ʳ-sym
                        ; trans = ≡ʳ-trans
                        }
      }

  -- the identity renaming
  idʳ : ∀ {Γ : Context} → Γ ⇒ʳ Γ
  idʳ x = x

  -- the canonical injection renamings
  inlʳ : ∀ {Γ Δ} → Γ ⇒ʳ Γ ,, Δ
  inlʳ = var-inl

  inrʳ : ∀ {Γ Δ} → Δ ⇒ʳ Γ ,, Δ
  inrʳ = var-inr

  -- composition of renamings
  _∘ʳ_ : ∀ {Γ Δ Ξ} → Δ ⇒ʳ Ξ → Γ ⇒ʳ Δ → Γ ⇒ʳ Ξ
  (σ ∘ʳ ρ) x = σ (ρ x)

  infix 7 _∘ʳ_

  -- composition respects equality
  ∘ʳ-resp-≡ʳ : ∀ {Γ Δ Ξ} {τ₁ τ₂ : Δ ⇒ʳ Ξ} {σ₁ σ₂ : Γ ⇒ʳ Δ} →
                 τ₁ ≡ʳ τ₂ → σ₁ ≡ʳ σ₂ → τ₁ ∘ʳ σ₁ ≡ʳ τ₂ ∘ʳ σ₂
  ∘ʳ-resp-≡ʳ {τ₁ = τ₁} {σ₂ = σ₂} ζ ξ x = trans (cong τ₁ (ξ x)) (ζ (σ₂ x))

  -- the identity is the unit

  identity-leftʳ : ∀ {Γ Δ} {ρ : Γ ⇒ʳ Δ} → idʳ ∘ʳ ρ ≡ʳ ρ
  identity-leftʳ ρ = refl

  identity-rightʳ : ∀ {Γ Δ} {ρ : Γ ⇒ʳ Δ} → ρ ∘ʳ idʳ ≡ʳ ρ
  identity-rightʳ ρ = refl

  -- composition is associative

  assocʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ʳ Δ} {ρ : Δ ⇒ʳ Ξ} {σ : Ξ ⇒ʳ Ψ} →
             (σ ∘ʳ ρ) ∘ʳ τ ≡ʳ σ ∘ʳ (ρ ∘ʳ τ)
  assocʳ x = refl

  sym-assocʳ : ∀ {Γ Δ Ξ Ψ} {τ : Γ ⇒ʳ Δ} {ρ : Δ ⇒ʳ Ξ} {σ : Ξ ⇒ʳ Ψ} →
             σ ∘ʳ (ρ ∘ʳ τ) ≡ʳ (σ ∘ʳ ρ) ∘ʳ τ
  sym-assocʳ x = refl

  -- contexts and renamings form a category
  module _ where
    open Categories.Category

    Contexts : Category ℓs ℓs ℓs
    Contexts =
      record
        { Obj = Context
        ; _⇒_ = _⇒ʳ_
        ; _≈_ = _≡ʳ_
        ; id = idʳ
        ; _∘_ = _∘ʳ_
        ; assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → assocʳ {τ = f} {ρ = g} {σ = h}
        ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} {_} → sym-assocʳ {τ = f} {ρ = g} {σ = h}
        ; identityˡ = λ x → refl
        ; identityʳ = λ x → refl
        ; identity² = λ x → refl
        ; equiv = record { refl = λ {ρ} {_} → ≡ʳ-refl {ρ = ρ} ; sym = ≡ʳ-sym ; trans = ≡ʳ-trans }
        ; ∘-resp-≈ = ∘ʳ-resp-≡ʳ
        }


  -- the coproduct structure of the category
  module _ where

    infixl 7 [_,_]ʳ

    [_,_]ʳ : ∀ {Γ Δ Ξ} → Γ ⇒ʳ Ξ → Δ ⇒ʳ Ξ → Γ ,, Δ ⇒ʳ Ξ
    [ σ , τ ]ʳ (var-inl x) = σ x
    [ σ , τ ]ʳ (var-inr y) = τ y

    uniqueʳ : ∀ {Γ Δ Ξ} {τ : Γ ,, Δ ⇒ʳ Ξ} {ρ : Γ ⇒ʳ Ξ} {σ : Δ ⇒ʳ Ξ}
              → τ ∘ʳ inlʳ ≡ʳ ρ
              → τ ∘ʳ inrʳ ≡ʳ σ
              → [ ρ , σ ]ʳ ≡ʳ τ
    uniqueʳ ξ ζ (var-inl x) = sym (ξ x)
    uniqueʳ ξ ζ (var-inr y) = sym (ζ y)

    Context-+ : Categories.Category.Cocartesian.BinaryCoproducts Contexts
    Context-+ =
      record {
        coproduct =
          λ {Γ Δ} →
          record
            { A+B = Γ ,, Δ
            ; i₁ = var-inl
            ; i₂ = var-inr
            ; [_,_] = [_,_]ʳ
            ; inject₁ = λ x → refl
            ; inject₂ = λ x → refl
            ; unique = uniqueʳ
            }
      }

  open Categories.Category.Cocartesian.BinaryCoproducts Context-+

  -- the action of a renaming on terms
  module _ {Θ : MetaContext} where

    infix 6 [_]ʳ_

    [_]ʳ_ : ∀ {Γ Δ A} → Γ ⇒ʳ Δ → Term Θ Γ A → Term Θ Δ A
    [ ρ ]ʳ (tm-var x) = tm-var (ρ x)
    [ ρ ]ʳ (tm-meta M ts) = tm-meta M (λ i → [ ρ ]ʳ (ts i))
    [ ρ ]ʳ (tm-oper f es) = tm-oper f (λ i → [ ρ +₁ idʳ ]ʳ (es i))

    -- weakening
    ⇑ʳ : ∀ {Γ Δ A} → Term Θ Γ A → Term Θ (Γ ,, Δ) A
    ⇑ʳ = [ i₁ ]ʳ_

  -- The sum of identities is an identity
  idʳ+idʳ : ∀ {Γ Δ} → idʳ {Γ = Γ} +₁ idʳ {Γ = Δ} ≡ʳ idʳ {Γ = Γ ,, Δ}
  idʳ+idʳ (var-inl x) = refl
  idʳ+idʳ (var-inr y) = refl

  -- The action of a renaming respects equality of terms
  []ʳ-resp-≈ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Γ ⇒ʳ Δ} → s ≈ t → [ ρ ]ʳ s ≈ [ ρ ]ʳ t
  []ʳ-resp-≈ (≈-≡ refl) = ≈-≡ refl
  []ʳ-resp-≈ (≈-meta ξ) = ≈-meta (λ i → []ʳ-resp-≈ (ξ i))
  []ʳ-resp-≈ (≈-oper ξ) = ≈-oper (λ i → []ʳ-resp-≈ (ξ i))

  -- The action of a renaming respects equality of renamings
  []ʳ-resp-≡ʳ : ∀ {Θ Γ Δ A} {ρ τ : Γ ⇒ʳ Δ} {t : Term Θ Γ A} → ρ ≡ʳ τ → [ ρ ]ʳ t ≈ [ τ ]ʳ t
  []ʳ-resp-≡ʳ {t = tm-var x} ξ = ≈-≡ (cong tm-var (ξ x))
  []ʳ-resp-≡ʳ {t = tm-meta M ts} ξ = ≈-meta (λ i → []ʳ-resp-≡ʳ ξ)
  []ʳ-resp-≡ʳ {t = tm-oper f es} ξ = ≈-oper (λ i → []ʳ-resp-≡ʳ (+₁-cong₂ ξ ≡ʳ-refl))

  -- The action of the identity is trival
  [id]ʳ : ∀ {Θ Γ A} {t : Term Θ Γ A} → [ idʳ ]ʳ t ≈ t
  [id]ʳ {t = tm-var x} = ≈-refl
  [id]ʳ {t = tm-meta M ts} = ≈-meta λ i → [id]ʳ
  [id]ʳ {t = tm-oper f es} = ≈-oper λ i → ≈-trans ([]ʳ-resp-≡ʳ idʳ+idʳ) [id]ʳ

  -- Summing with identity respects composition
  ∘ʳ-+₁-idʳ : ∀ {Γ Δ Ξ Ψ} {ρ : Γ ⇒ʳ Δ} {τ : Δ ⇒ʳ Ξ} → (τ ∘ʳ ρ) +₁ idʳ {Γ = Ψ} ≡ʳ (τ +₁ idʳ) ∘ʳ (ρ +₁ idʳ)
  ∘ʳ-+₁-idʳ (var-inl x) = refl
  ∘ʳ-+₁-idʳ (var-inr y) = refl

  -- The action of a renaming is functorial
  [∘]ʳ : ∀ {Θ Γ Δ Ξ} {ρ : Γ ⇒ʳ Δ} {τ : Δ ⇒ʳ Ξ} {A} {t : Term Θ Γ A} → [ τ ∘ʳ ρ ]ʳ t ≈ [ τ ]ʳ ([ ρ ]ʳ t)
  [∘]ʳ {t = tm-var x} = ≈-refl
  [∘]ʳ {t = tm-meta M ts} = ≈-meta (λ i → [∘]ʳ)
  [∘]ʳ {t = tm-oper f es} = ≈-oper (λ i → ≈-trans ([]ʳ-resp-≡ʳ ∘ʳ-+₁-idʳ) [∘]ʳ)

  -- Forming terms over a given metacontext and sort is functorial in the context,
  -- and even a relative monad
  module _ {Θ : MetaContext} {A : sort} where
    open Categories.Functor
    open Categories.Category.Instance.Setoids
    open Categories.Monad.Relative

    Term-Functor : Functor Contexts (Setoids (lsuc (ℓs ⊔ ℓo)) (lsuc (ℓs ⊔ ℓo)))
    Term-Functor =
      record
        { F₀ = λ Γ → Term-setoid Θ Γ A
        ; F₁ = λ ρ → record { _⟨$⟩_ = [ ρ ]ʳ_ ; cong = []ʳ-resp-≈ }
        ; identity = ≈-trans [id]ʳ
        ; homomorphism = λ ξ → ≈-trans ([]ʳ-resp-≈ ξ) [∘]ʳ
        ; F-resp-≈ = λ ζ ξ → ≈-trans ([]ʳ-resp-≡ʳ ζ) ([]ʳ-resp-≈ ξ)
        }

    -- The embedding of contexts into setoids
    slots : Functor Contexts (Setoids (ℓs ⊔ ℓo) ℓs)
    slots = record
              { F₀ = λ Γ → setoid (A ∈ Γ)
              ; F₁ = λ ρ → record { _⟨$⟩_ = ρ ; cong = cong ρ }
              ; identity = λ ξ → ξ
              ; homomorphism = λ {_} {_} {_} {f = f} {g = g} {_} {_} ξ → cong g (cong f ξ)
              ; F-resp-≈ = λ ζ ξ → trans (ζ _) (cong _ ξ)
              }

    Term-Monad : Monad slots
    Term-Monad =
      record
        { F₀ = λ Γ → {!Term-setoid Θ Γ A!}
        ; unit = {!!}
        ; extend = {!!}
        ; identityʳ = {!!}
        ; identityˡ = {!!}
        ; assoc = {!!}
        ; extend-≈ = {!!}
        }



    -- -- -- apply the reassociation renaming on terms
    -- -- term-reassoc : ∀ {Δ Γ Ξ A}
    -- --   → Term Θ (Δ ,, (Γ ,, Ξ)) A
    -- --   → Term Θ ((Δ ,, Γ) ,, Ξ) A
    -- -- term-reassoc = [ rename-assoc ]ʳ_

--   -- a renaming can be extended on the right
--   extendʳ : ∀ {Γ Δ} → Γ ⇒ʳ Δ → ∀ {Ξ} → Γ ,, Ξ ⇒ʳ Δ ,, Ξ
--   extendʳ ρ (var-inl x) = var-inl (ρ x)
--   extendʳ ρ (var-inr y) = var-inr y

--   -- the reassociation renaming

--   rename-assoc : ∀ {Γ Δ Ξ} → Γ ,, (Δ ,, Ξ) ⇒ʳ (Γ ,, Δ) ,, Ξ
--   rename-assoc (var-inl x) = var-inl (var-inl x)
--   rename-assoc (var-inr (var-inl y)) = var-inl (var-inr y)
--   rename-assoc (var-inr (var-inr z)) = var-inr z

--   -- the inverse of the reassociation renaming

--   rename-unassoc : ∀ {Γ Δ Ξ} → (Γ ,, Δ) ,, Ξ ⇒ʳ Γ ,, (Δ ,, Ξ)
--   rename-unassoc (var-inl (var-inl x)) = var-inl x
--   rename-unassoc (var-inl (var-inr x)) = var-inr (var-inl x)
--   rename-unassoc (var-inr x) = var-inr (var-inr x)

--   -- the empty context is the right unit

--   ctx-empty-right-unit : ∀ {Γ} → Γ ,, ctx-empty ⇒ʳ Γ
--   ctx-empty-right-unit (var-inl x) = x

--   rename-ctx-empty-inv : ∀ {Γ} → Γ ⇒ʳ Γ ,, ctx-empty
--   rename-ctx-empty-inv x = var-inl x

--   -- the empty context is the left unit

--   ctx-empty-left-unit : ∀ {Γ} → ctx-empty ,, Γ ⇒ʳ Γ
--   ctx-empty-left-unit (var-inr x) = x


--   module _ {Θ : MetaContext} where

--     -- action of a renaming on terms
--     [_]ʳ_ : ∀ {Γ Δ A} → Γ ⇒ʳ Δ → Term Θ Γ A → Term Θ Δ A
--     [ ρ ]ʳ (tm-var x) = tm-var (ρ x)
--     [ ρ ]ʳ (tm-meta M ts) = tm-meta M (λ i → [ ρ ]ʳ (ts i))
--     [ ρ ]ʳ (tm-oper f es) = tm-oper f (λ i → [ (extendʳ ρ) ]ʳ (es i))

--     infix 6 [_]ʳ_

--     -- apply the reassociation renaming on terms
--     term-reassoc : ∀ {Δ Γ Ξ A}
--       → Term Θ (Δ ,, (Γ ,, Ξ)) A
--       → Term Θ ((Δ ,, Γ) ,, Ξ) A
--     term-reassoc = [ rename-assoc ]ʳ_

--     -- weakening
--     ⇑ʳ : ∀ {Γ Δ A} → Term Θ Γ A → Term Θ (Γ ,, Δ) A
--     ⇑ʳ = [ var-inl ]ʳ_


-- --========================================================================================
-- --∥                              ========================                                ∥
-- --∥                              ∥  ** METATHEOREMS **  ∥                                ∥
-- --∥                              ========================                                ∥
-- --========================================================================================

--   -- association and unassociation renamings are inverses of each other
--   rename-assoc-inv : ∀ {Γ Δ Ξ} → rename-assoc {Γ} {Δ} {Ξ} ∘ʳ rename-unassoc ≡ʳ idʳ
--   rename-assoc-inv (var-inl (var-inl x)) = refl
--   rename-assoc-inv (var-inl (var-inr y)) = refl
--   rename-assoc-inv (var-inr z) = refl

--   rename-unassoc-inv : ∀ {Γ Δ Ξ} → rename-unassoc {Γ} {Δ} {Ξ} ∘ʳ rename-assoc ≡ʳ idʳ
--   rename-unassoc-inv (var-inl x) = refl
--   rename-unassoc-inv (var-inr (var-inl y)) = refl
--   rename-unassoc-inv (var-inr (var-inr z)) = refl


--   -------------------------------------------
--   --          Lemmas about joins           --
--   -------------------------------------------

--   -- We want to show that sums of renamings form a coproduct of morphisms
--   -- in the category where Contexts are the objects and renamings the morphisms
--   -- between them.

--   -- The join of two renamings gives us the renaming prophesied by the
--   -- universal property of coproducts.
--   -- Now we just need to show uniqueness:
--   unique⋈ʳ : ∀ {Γ Δ Ξ} {ρ : Γ ⇒ʳ Ξ} {ν : Δ ⇒ʳ Ξ} {δ : Γ ,, Δ ⇒ʳ Ξ}
--           → (δ ∘ʳ inlʳ) ≡ʳ ρ
--           → (δ ∘ʳ inrʳ) ≡ʳ ν
--           → δ ≡ʳ (ρ ⋈ʳ ν)
--   unique⋈ʳ eq1 eq2 (var-inl x) = eq1 x
--   unique⋈ʳ eq1 eq2 (var-inr y) = eq2 y

--   unique-cotupleʳ : ∀ {Γ Δ Ξ} {ρ : Γ ⇒ʳ Ξ} {ν : Δ ⇒ʳ Ξ} {γ δ : Γ ,, Δ ⇒ʳ Ξ}
--                  → γ ∘ʳ inlʳ ≡ʳ ρ → γ ∘ʳ inrʳ ≡ʳ ν
--                  → δ ∘ʳ inlʳ ≡ʳ ρ → δ ∘ʳ inrʳ ≡ʳ ν
--                  → γ ≡ʳ δ
--   unique-cotupleʳ {γ = γ} {δ = δ} eq1 eq2 eq3 eq4 (var-inl x) = ≡ʳ-trans eq1 (≡ʳ-sym eq3) x
--   unique-cotupleʳ {γ = γ} {δ = δ} eq1 eq2 eq3 eq4 (var-inr y) = ≡ʳ-trans eq2 (≡ʳ-sym eq4) y

--   -------------------------------------------
--   --          Lemmas about sums            --
--   -------------------------------------------

--   -- We have existance of coproducts of renamings with the sum
--   -- once again, what about uniqueness?
--   -- For any renaming ρ : Γ ,, Γ' → Δ ,, Δ' that makes the corresponding
--   -- squares commute, we have ρ ≡ʳ σ +ʳ τ
--   unique+ʳ : ∀ {Γ Γ' Δ Δ'} {ρ : Γ ⇒ʳ Δ} {ν : Γ' ⇒ʳ Δ'} {γ δ : Γ ,, Γ' ⇒ʳ Δ ,, Δ'}
--              → γ ∘ʳ inlʳ ≡ʳ inlʳ ∘ʳ ρ
--              → γ ∘ʳ inrʳ ≡ʳ inrʳ ∘ʳ ν
--              → δ ∘ʳ inlʳ ≡ʳ inlʳ ∘ʳ ρ
--              → δ ∘ʳ inrʳ ≡ʳ inrʳ ∘ʳ ν
--              → γ ≡ʳ δ
--   unique+ʳ {ρ = ρ} {ν = ν} {γ = γ} {δ = δ} eq1 eq2 eq3 eq4 = unique-cotupleʳ {γ = γ} {δ = δ} eq1 eq2 eq3 eq4

--   unique+ : ∀ {Γ Γ' Δ Δ' Ξ Λ} {ρ : Γ ⇒ʳ Δ} {ν : Γ' ⇒ʳ Δ'} {δ : Ξ ⇒ʳ Λ}
--     → (α₁ : Γ ⇒ʳ Ξ) → (α₂ : Δ ⇒ʳ Λ) → (δ ∘ʳ α₁) ≡ʳ (α₂ ∘ʳ ρ)
--     → (β₁ : Γ' ⇒ʳ Ξ) → (β₂ : Δ' ⇒ʳ Λ) → (δ ∘ʳ β₁) ≡ʳ (β₂ ∘ʳ ν)
--     → δ ∘ʳ (α₁ ⋈ʳ β₁) ≡ʳ (α₂ ⋈ʳ β₂) ∘ʳ (ρ +ʳ ν)
--   unique+ α₁ α₂ eq1 β₁ β₂ eq2 (var-inl x) = eq1 x
--   unique+ α₁ α₂ eq1 β₁ β₂ eq2 (var-inr y) = eq2 y


--   -- Lemma: The extension of a renaming is equal to summing with the identity renaming
--   extendʳ≡+id : ∀ {Γ Δ Ξ} {ρ : Γ ⇒ʳ Δ}
--              → (extendʳ ρ {Ξ}) ≡ʳ (ρ +ʳ idʳ)
--   extendʳ≡+id (var-inl x) = refl
--   extendʳ≡+id (var-inr y) = refl

--   -- Lemma: The sum of two equal renamings is equal
--   ≡ʳ+ʳ : ∀ {Γ Δ Ξ Λ} {ρ ρ' : Γ ⇒ʳ Δ} {ν ν' : Ξ ⇒ʳ Λ}
--        → ρ ≡ʳ ρ' → ν ≡ʳ ν'
--        → (ρ +ʳ ν) ≡ʳ (ρ' +ʳ ν')
--   ≡ʳ+ʳ eq1 eq2 (var-inl x) = cong var-inl (eq1 x)
--   ≡ʳ+ʳ eq1 eq2 (var-inr y) = cong var-inr (eq2 y)

--   -- (1) the extension of to equal renamings are equal
--   ≡ʳextendʳ : ∀ {Γ Δ Ξ} {ρ ν : Γ ⇒ʳ Δ}
--         → ρ ≡ʳ ν → extendʳ ρ {Ξ = Ξ} ≡ʳ extendʳ ν
--   ≡ʳextendʳ p (var-inl x) = ≡-inl (p x)
--   ≡ʳextendʳ p (var-inr x) = refl

--   -- (2) two equal renamings have the same action
--   ≈ʳ[]ʳ : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {ρ ν : Γ ⇒ʳ Δ}
--         → ρ ≡ʳ ν → [ ρ ]ʳ t ≈ [ ν ]ʳ t
--   ≈ʳ[]ʳ {t = tm-var x} p = ≈-≡ (≡-var (p x))
--   ≈ʳ[]ʳ {t = tm-meta M ts} p = ≈-meta λ i → ≈ʳ[]ʳ p
--   ≈ʳ[]ʳ {Θ} {A = A} {t = tm-oper f es} p = ≈-oper (λ i → ≈ʳ[]ʳ (≡ʳextendʳ p))

--   -- (3) the extension of a composition is equal to the composition of extensions
--   ∘r-≈-extendʳ : ∀ {Γ Δ Λ Ξ} (ρ : Γ ⇒ʳ Δ) (ν : Δ ⇒ʳ Λ)
--         →  extendʳ (ν ∘ʳ ρ) {Ξ = Ξ} ≡ʳ ((extendʳ ν) ∘ʳ (extendʳ ρ))
--   ∘r-≈-extendʳ ρ ν (var-inl x) = refl
--   ∘r-≈-extendʳ ρ ν (var-inr x) = refl

--   -- (4) composition of renamings commutes with equality
--   ∘r-≈ : ∀ {Θ Γ Δ Ξ A} (t : Term Θ Γ A) (ρ : Γ ⇒ʳ Δ) (ν : Δ ⇒ʳ Ξ)
--         → [ ν ∘ʳ ρ ]ʳ t ≈ [ ν ]ʳ ([ ρ ]ʳ t)
--   ∘r-≈ (tm-var x) ρ ν = ≈-refl
--   ∘r-≈ (tm-meta M ts) ρ ν = ≈-meta (λ i → ∘r-≈ (ts i) ρ ν)
--   ∘r-≈ (tm-oper f es) ρ ν = ≈-oper λ i → ≈-trans
--                                            (≈ʳ[]ʳ (∘r-≈-extendʳ ρ ν))
--                                            (∘r-≈ (es i) (extendʳ ρ) (extendʳ ν))


--   -- (5) the action of the identity renaming is the identity
--   -- auxiliary function for (5), to deal with extensions in the oper case
--   -- the extension of the identity is the identity
--   idʳextendʳ : ∀ {Γ Ξ} → extendʳ (idʳ {Γ = Γ})  {Ξ = Ξ}  ≡ʳ idʳ
--   idʳextendʳ (var-inl x) = refl
--   idʳextendʳ (var-inr x) = refl

--   -- (5)
--   []ʳidʳ : ∀ {Θ Γ A} (t : Term Θ Γ A)
--           → [ idʳ ]ʳ t ≈ t
--   []ʳidʳ (tm-var x) = ≈-≡ refl
--   []ʳidʳ (tm-meta M ts) = ≈-meta λ i → []ʳidʳ (ts i)
--   []ʳidʳ (tm-oper f es) = ≈-oper λ i → ≈-trans
--                                        (≈ʳ[]ʳ idʳextendʳ)
--                                        ([]ʳidʳ (es i))

--   -- (6) renamings preserve syntactical equality of terms
--   ≈-tm-ʳ : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : Γ ⇒ʳ Δ}
--         → s ≈ t → [ ρ ]ʳ s ≈ [ ρ ]ʳ t
--   ≈-tm-ʳ (≈-≡ refl) = ≈-≡ refl
--   ≈-tm-ʳ (≈-meta ξ) = ≈-meta (λ i → ≈-tm-ʳ (ξ i))
--   ≈-tm-ʳ (≈-oper ξ) = ≈-oper (λ i → ≈-tm-ʳ (ξ i))


--   -- interactions between "reassociation" and "unassociation"
--   -- (the functions that change the way the concatenation of context is associated)
--   -- the reassociation renaming and "unassociation" renaming are inverse
--   unassoc-reassoc : ∀ {Γ Δ Ξ} → (rename-unassoc {Δ} {Γ} {Ξ}) ∘ʳ rename-assoc ≡ʳ idʳ
--   unassoc-reassoc (var-inl x) = refl
--   unassoc-reassoc (var-inr (var-inl x)) = refl
--   unassoc-reassoc (var-inr (var-inr x)) = refl

--   -- "reassociating" and then "unassociating" a term acts like the identity
--   unassoc-reassoc-tm : ∀ {Θ Γ Δ Ξ A} (t : Term Θ (Γ ,, (Δ ,, Ξ)) A) → [ rename-unassoc ]ʳ (term-reassoc t) ≈ t
--   unassoc-reassoc-tm t = ≈-trans
--                            (≈-trans
--                              (≈-sym (∘r-≈ t rename-assoc rename-unassoc))
--                              (≈ʳ[]ʳ unassoc-reassoc))
--                            ([]ʳidʳ t)

--   -- term-reassociation preserves syntactical equality of terms
--   ≈-tm-reassoc : ∀ {Θ Γ Δ Ξ A} {s t : Term Θ (Γ ,, (Δ ,, Ξ)) A}
--                  → term-reassoc s ≈ term-reassoc t → s ≈ t
--   ≈-tm-reassoc {s = s} {t = t} p = ≈-trans
--                                      (≈-sym (unassoc-reassoc-tm s))
--                                      (≈-sym (≈-trans
--                                        (≈-sym (unassoc-reassoc-tm t))
--                                        (≈-tm-ʳ (≈-sym p))))

--   -- extending two times is like extending one time and unassociating
--   extendʳ² : ∀ {Γ Δ Ξ Λ Ω} (ρ : Γ ,, Δ ⇒ʳ Ω)
--              → (rename-unassoc {Δ = Ξ} {Ξ = Λ}) ∘ʳ (extendʳ  (extendʳ ρ)) ≡ʳ (extendʳ ρ) ∘ʳ rename-unassoc
--   extendʳ² ρ (var-inl (var-inl x)) = refl
--   extendʳ² ρ (var-inl (var-inr x)) = refl
--   extendʳ² ρ (var-inr x) = refl
