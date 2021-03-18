open import Relation.Binary.PropositionalEquality

open import Agda.Primitive
open import Data.Fin hiding (_+_)
open import Data.Sum.Base
open import Agda.Builtin.Nat

import Categories.Category as Category
import Categories.Category.Cartesian as Cartesian

open import SingleSorted.AlgebraicTheory
import SingleSorted.Interpretation as Interpretation
import SingleSorted.Model as Model
import SingleSorted.Substitution as Substitution
import SingleSorted.FactsCartesian as FactsCartesian

open import SingleSorted.FactsFinite

module SingleSorted.SyntacticCategory {ℓt}
  {Σ : Signature}
  (T : Theory ℓt Σ) where

  open Signature Σ
  open Theory T
  open Substitution T

  -- The syntactic category

  𝒮 : Category.Category lzero lzero (lsuc ℓt)
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


  ≡-eq-refl : ∀ {Γ : Context} {s : Term Γ} {t : Term Γ} → s ≡ t → Γ ⊢ s ≈ t
  ≡-eq-refl refl = eq-refl

  -- This should later go in another file, probably FactsFinite.agda, but for the moment it was easier to write it there
  pre-unique : ∀ {Γ Δ C : Context} {h  : substitution Σ C (Δ + Γ)} {i  : substitution Σ C Γ} {j  : substitution Σ C Δ} {p₁ : (λ x → h (raise Δ x)) ≈s i} {p₂ : (λ x₁ → h (inject+ Γ x₁)) ≈s j} {x  : var (Δ + Γ)} → (C ⊢ ([ j , i ] (splitAt Δ x)) ≈ (h x))
  pre-unique {Δ = zero} {h = h} {i = i} {p₁ = p₁} {x = zero} = equiv-subst i h (symm-subst p₁) (tm-var zero)
  pre-unique {Δ = zero} {h = h} {i = i} {p₁ = p₁} {x = suc x} = equiv-subst i h (symm-subst p₁) (tm-var (suc x))
  pre-unique {Γ} {Δ = suc Δ} {h = h} {j = j} {p₂ = p₂} {x = zero} = equiv-subst j (λ x → h (inject+ Γ x)) (symm-subst p₂) (tm-var zero)
  pre-unique {Δ = suc Δ} {h = h} {i} {j} {p₁} {p₂} {x = suc x} = eq-tran (≡-eq-refl {!!}) (pre-unique {Δ = Δ} {h = λ x₁ → h (suc x₁)} {i} {λ x₁ → j (suc x₁)} {p₁} {λ x₁ → (p₂ (suc x₁))} {x = x})
-- [ j , i ] (map suc (λ x₁ → x₁) (splitAt Δ x)) ≡
-- [ (λ x₁ → j (suc x₁)) , i ] (splitAt Δ x)

  cartesian-𝒮 : Cartesian.Cartesian 𝒮
  cartesian-𝒮 =
    record { terminal = record { ⊤ = empty-context
                               ; ⊤-is-terminal = record { ! = empty-context-absurd
                                                        ; !-unique = λ f → empty-context-unique
                                                        }
                               }
           ; products =  record { product =  λ {Γ} {Δ} → record
                                                           { A×B =  Δ + Γ
                                                           ; π₁ =  λ x → tm-var (raise Δ x)
                                                           ; π₂ = λ x → tm-var (inject+ Γ x)
                                                           ; ⟨_,_⟩ = λ f g x → [ g , f ] (splitAt Δ x)
                                                           ; project₁ = λ {h = s} {i = h} {i} x → ≡-eq-refl (proj₁ T {Γ = Γ} {Δ} {s} {x} {h} {i})
                                                           ; project₂ = λ {h = s} {i = h} {i} x → ≡-eq-refl (proj₂ T {Γ = Γ} {Δ} {s} {x} {h} {i})
                                                           ; unique = λ {C} {h} {i} {j} p₁ p₂ x → pre-unique {Γ} {Δ} {C} {h} {i} {j} {p₁} {p₂}
                                                           } }
           }


  open FactsCartesian cartesian-𝒮

  -- Pow in the Syntactic Category
  pow-𝒮 : ∀ {a : Nat} → pow 1 a ≡ a
  pow-𝒮 {zero} = refl
  pow-𝒮 {suc a} = cong suc pow-𝒮

  transport-pow-𝒮 : ∀ {a : Nat} (x : var (a)) →  var (pow 1 a)
  transport-pow-𝒮 = subst var (sym pow-𝒮)


  -- The universal interpretation

  UniversalI : Interpretation.Interpretation Σ cartesian-𝒮
  UniversalI =
    let open Category.Category 𝒮 in
    record { interp-carrier = 1
           ; interp-oper =  λ f x → tm-oper f (λ y → tm-var (transport-pow-𝒮 {oper-arity f} y))
           }

  -- The syntactic category "preserves" the equivalence of terms
  module _ where
    open Category.Category 𝒮
    open Interpretation.Interpretation UniversalI

    𝒮-respect-≈ : ∀ {Γ : Context} {u v : Term Γ} → (Γ ⊢ u ≈ v) → (interp-term u) ≈s (interp-term v)
    𝒮-respect-≈ Theory.eq-refl = λ x → eq-refl
    𝒮-respect-≈ (Theory.eq-symm p) = symm-subst (𝒮-respect-≈ p)
    𝒮-respect-≈ (Theory.eq-tran p₁ p₂) = trans-subst (𝒮-respect-≈ p₁) (𝒮-respect-≈ p₂)
    𝒮-respect-≈ (Theory.eq-congr {_} {f} {xs} {ys} ps) = ∘-resp-≈ {f = interp-oper f} {h = interp-oper f} {g = pow-tuple (λ i → interp-term (xs i))} {i = pow-tuple (λ i → interp-term (ys i))} (refl-subst) (pow-tuple-eq (λ i x → 𝒮-respect-≈ (ps i) x))
    𝒮-respect-≈ (Theory.eq-axiom ε σ) = {!!}
    -- First attempt (didn't work) : λ x → eq-tran (𝒮-respect-subst (eq-lhs ε) σ x) (eq-symm (eq-tran (𝒮-respect-subst (eq-rhs ε) σ x) (eq-subst  (lift-subst σ) {u = (interp-term UniversalI (eq-rhs ε)) x} {v = (interp-term UniversalI (eq-lhs ε)) x} (𝒮-respect-≈ {u = (eq-rhs ε)} {v = (eq-lhs ε)} {!!} {!!}))))

    -- The universal model
    UniversalM : Model.Model T UniversalI
    UniversalM =
      record
        { model-eq =
             λ ε x → equiv-subst (interp-term (eq-lhs ε)) (interp-term (eq-rhs ε)) (𝒮-respect-≈ {u = eq-lhs ε} {v = eq-rhs ε} (eq-id-action (eq-axiom ε id-substitution))) (tm-var x)
        }