open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Data.Fin
open import Data.Sum.Base
open import Data.Nat.Properties
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong-app; trans) renaming (sym to symm)
open Eq.≡-Reasoning

open import Categories.Category
open import Categories.Category.Cartesian

open import SingleSorted.AlgebraicTheory
open import SingleSorted.Interpretation

module SingleSorted.Model {ℓt} {Σ : Signature} (T : Theory ℓt Σ) where

  open Signature Σ
  open Theory T

  postulate
    funext : ∀ {l : Level} {X : Set l} {Y : X → Set l} {f g : ∀ (x : X) → (Y x)} → (∀ (x : X) → ((f x) ≡ (g x))) → (f ≡ g)

  congr : ∀ {l : Level} {X Y : Set l} {f : ∀ (x : X) → Y} {x y : X} → (x ≡ y) → (f x ≡ f y)
  congr refl = refl

  eq-builtin-refl : ∀ {l : Level} {Γ : Context} {x : Term Γ} {y : Term Γ} → (x ≡ y) → (Γ ⊢ x ≈ y)
  eq-builtin-refl refl = eq-refl


  -- Model of a theory

  record Model {o ℓ e} {𝒞 : Category o ℓ e} {cartesian-𝒞 : Cartesian 𝒞}
            (I : Interpretation Σ cartesian-𝒞) : Set (ℓt ⊔ o ⊔ ℓ ⊔ e) where

    open Interpretation I
    open Category 𝒞

    field
      model-eq : ∀ (ε : eq) → interp-term (eq-lhs ε) ≈ interp-term (eq-rhs ε)

  -- Every theory has the trivial model, whose carrier is the terminal object
  TrivialM : ∀ {o ℓ e} {𝒞 : Category o ℓ e} (cartesian-𝒞 : Cartesian 𝒞) → Model (TrivialI Σ cartesian-𝒞)
  TrivialM cart =
     let open Cartesian cart in
     record { model-eq = λ ε → !-unique₂ }





  -- The syntactic category

  𝒮 : Category lzero lzero (lsuc ℓt)
  𝒮 =
    record
      { Obj = Context
      ; _⇒_ = substitution Σ
      ; _≈_ = _≈s_
      ; id =  id-substitution
      ; _∘_ =  _∘s_
      ; assoc = λ {A B C D f g h} x →  subst-∘s ((tm-var x) [ h ]s)
      ; sym-assoc =  λ {A B C D f g h} x → eq-symm (subst-∘s ((tm-var x) [ h ]s))
      ; identityˡ = λ x → eq-refl
      ; identityʳ = λ {A B f} x →  tm-var-id
      ; identity² = λ x → eq-refl
      ; equiv = record { refl = λ x → eq-refl
               ; sym = λ {x = x} {y = y} a b → equiv-subst y x (symm-subst a) (tm-var b)
               ; trans = λ {i = i} {j = j} {k = k} a b c → equiv-subst i k (trans-subst a b) (tm-var c) }
      ; ∘-resp-≈ = λ {A B C f h g i} x x₁ x₂ → equiv-eq-subst g i x₁ (x x₂)
      }





  -- The cartesian structure of the syntactic category

  _plus_ : Nat → Nat → Nat
  _plus_ = Agda.Builtin.Nat._+_

  com+ = +-comm

  -- handling finite sets
  swap-Fin : ∀ {Γ Δ} → Fin (Γ plus Δ) → Fin (Δ plus Γ)
  swap-Fin {Γ} {Δ} = λ  x → cast (com+ Γ Δ) x

  lift-prod₁ : ∀ {Δ Γ} → Fin Γ → Fin (Γ plus Δ)
  lift-prod₁ {Δ} {Γ} a = swap-Fin {Δ} {Γ} (raise Δ a)

  lift-prod₂ : ∀ {Δ Γ} → Fin Δ → Fin (Γ plus Δ)
  lift-prod₂ {Δ} {Γ} a =  swap-Fin {Δ} {Γ}(inject+ Γ a)


  -- useful to define "project₁" and "project₂"
  pre-proj₁ : ∀ {Γ Δ : Nat}  {x : Fin Γ} → (splitAt Γ (lift-prod₁ {Δ} {Γ} x)) ≡ (inj₁ x)
  pre-proj₁ = {!!}
  -- I am pretty conviced that the above works, but not sure because I struggle to prove it

  proj₁ :  ∀ {Γ Δ A : Context}  {x : Fin Γ} {h : substitution Σ A Γ } {i : substitution Σ A Δ} → [ h , i ] (splitAt Γ (lift-prod₁ {Δ} {Γ} x)) ≡ h x
  proj₁ {Γ} {Δ} {A} {x} {h} {i} = trans (congr {f = [ h , i ]} {x = (splitAt Γ (lift-prod₁ {Δ} {Γ} x))} {y = inj₁ x} (pre-proj₁ {Γ} {Δ} {x})) refl

  pre-proj₂ : ∀ {Γ  Δ : Nat}  {x : Fin Δ} → (splitAt Γ (lift-prod₂ {Δ} {Γ} x)) ≡ (inj₂ x)
  pre-proj₂ = {!!}

  proj₂ :  ∀ {Γ Δ A : Context}  {x : Fin Δ} {h : substitution Σ A Γ } {i : substitution Σ A Δ} → [ h , i ] (splitAt Γ (lift-prod₂ {Δ} {Γ} x)) ≡ i x
  proj₂ {Γ} {Δ} {A} {x} {h} {i} = trans (congr {f = [ h , i ]} {x = (splitAt Γ (lift-prod₂ {Δ} {Γ} x))} {y = inj₂ x} (pre-proj₂ {Γ} {Δ} {x})) refl

  -- Cartesian structure of 𝒮
  cartesian-𝒮 : Cartesian 𝒮
  cartesian-𝒮 =
    record { terminal = record { ⊤ = empty-context
                               ; ⊤-is-terminal = record { ! = empty-context-absurd
                                                        ; !-unique = λ f → empty-context-unique
                                                        }
                               }
           ; products =  record { product =  λ {Γ} {Δ} → record
                                                           { A×B =  Γ plus Δ
                                                           ; π₁ = λ x → tm-var (lift-prod₁ x)
                                                           ; π₂ = λ x → tm-var (lift-prod₂ x)
                                                           ; ⟨_,_⟩ = λ x x₁ x₂ → [ x , x₁ ] (splitAt Γ x₂)
                                                           ; project₁ = λ {h = s} {i = h} {i} x → eq-builtin-refl {ℓt} {Γ = s} {x = [ h , i ] (splitAt Γ (lift-prod₁ {Δ} {Γ} x)) } {y = h x} (proj₁{Γ} {Δ} {s} {x} {h} {i})
                                                           ; project₂ = λ {h = s} {i = h} {i} x → eq-builtin-refl {ℓt} {Γ = s} {x = [ h , i ] (splitAt Γ (lift-prod₂ {Δ} {Γ} x)) } {y = i x} (proj₂{Γ} {Δ} {s} {x} {h} {i})
                                                           ; unique = λ {C} {h} {i} {j} p₁ p₂ x → eq-builtin-refl {ℓt} {!!}
                                                           } }
           }

  -- The universal interpretation
  ×-comm = BinaryProducts.×-comm

  pow-𝒮 : ∀ {a : Nat} → ((pow Σ cartesian-𝒮 1 a) ≡ a)
  pow-𝒮 {zero} = refl
  pow-𝒮 {suc n} = trans (com+ (pow Σ cartesian-𝒮 1 n) 1) (congr {f = suc} pow-𝒮)

  transport-pow-𝒮 : ∀ {a : Nat} (x : var (a)) →  var (pow Σ cartesian-𝒮 1 a)
  transport-pow-𝒮 = Eq.subst var (symm pow-𝒮)

  universalI : Interpretation Σ cartesian-𝒮
  universalI =
    let open Category 𝒮 in
    record { interp-carrier = 1
           ; interp-oper =  λ f x → tm-oper f (λ y → tm-var (transport-pow-𝒮 {oper-arity f} y))
           }

  interp-term = Interpretation.interp-term
  interp-oper = Interpretation.interp-oper

  -- 𝒮-respect-subst : ∀ {Γ : Context} (u : Term {Σ} Γ) → (interp-term universalI () -- first define the "interpretation of a substitution"

  𝒮-respect-≈ : ∀ {Γ : Context} {u v : Term {Σ} Γ} → (Γ ⊢ u ≈ v) → (interp-term universalI u) ≈s (interp-term universalI v)
  𝒮-respect-≈ Theory.eq-refl = λ x → eq-refl
  𝒮-respect-≈ (Theory.eq-symm p) = symm-subst (𝒮-respect-≈ p)
  𝒮-respect-≈ (Theory.eq-tran p₁ p₂) = trans-subst (𝒮-respect-≈ p₁) (𝒮-respect-≈ p₂)
  𝒮-respect-≈ (Theory.eq-congr {Γ} {f} {xs} {ys} ps) =  Category.∘-resp-≈ 𝒮 {f = interp-oper universalI f} {h = interp-oper universalI f} {g = pow-tuple Σ cartesian-𝒮 (λ i → interp-term universalI (xs i))} {i = pow-tuple Σ cartesian-𝒮 (λ i → interp-term universalI (ys i))} (refl-subst) (pow-tuple-eq Σ cartesian-𝒮 (λ i x → 𝒮-respect-≈ (ps i) x))
  𝒮-respect-≈ (Theory.eq-axiom ε σ) = {!!} -- 𝒮-respect-≈ (eq-subst σ {u = eq-lhs ε} {v = eq-rhs ε} {!!}) -- Here, I think that we want to show that the interpretation "commutes" (wrt ≈) with substitution (interpreted substitution in fact)

  -- The universal model
  UniversalM : Model universalI
  UniversalM = record { model-eq = λ ε x → equiv-subst (interp-term universalI (eq-lhs ε)) (interp-term universalI (eq-rhs ε)) (𝒮-respect-≈ {u = eq-lhs ε} {v = eq-rhs ε} {!!}) {!!}}
