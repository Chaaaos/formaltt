open import SingleSorted.AlgebraicTheory
open import SingleSorted.Interpretation using (Interpretation; TrivialI)
module SingleSorted.SyntacticCategory {ℓt} {Σ : Signature} (T : Theory ℓt Σ) where

  open import SingleSorted.Model public
  open import Data.Fin renaming (_+_ to _+ᶠ_)

  open Signature Σ
  open Theory T

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

  cartesian-𝒮 : Cartesian 𝒮
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
                                                           ; ⟨_,_⟩ = λ f g x → [ g ⊎ f ] (splitAt Δ x)
                                                           ; project₁ = λ {h = s} {i = h} {i} x → eq-builtin-refl {ℓt} {Σ} T {ℓt} {Γ = s} {x = [ i ⊎ h ] (splitAt Δ (raise Δ x)) } {y = h x} (proj₁ T {Γ = Γ} {Δ} {s} {x} {h} {i})
                                                           ; project₂ = λ {h = s} {i = h} {i} x → eq-builtin-refl {ℓt} {Σ} T {ℓt} {Γ = s} {x = [ i ⊎ h ] (splitAt Δ (inject+ Γ x)) } {y = i x} ((proj₂ T {Γ = Γ} {Δ} {s} {x} {h} {i}))
                                                           ; unique = {!!} -- λ {C} {h} {i} {j} p₁ p₂ x → eq-builtin-refl {ℓt} {!!}
                                                           } }
           }



  -- Pow in the Syntactic Category
  pow-𝒮 : ∀ {a : Nat} → ((pow Σ cartesian-𝒮 1 a) ≡ a)
  pow-𝒮 {zero} = refl
  pow-𝒮 {suc a} = congr T {f = suc} pow-𝒮

  transport-pow-𝒮 : ∀ {a : Nat} (x : var (a)) →  var (pow Σ cartesian-𝒮 1 a)
  transport-pow-𝒮 = subst var (symm pow-𝒮)


  -- The universal interpretation
  interp-term = Interpretation.interp-term
  interp-oper = Interpretation.interp-oper

  universalI : Interpretation Σ cartesian-𝒮
  universalI =
    let open Category 𝒮 in
    record { interp-carrier = 1
           ; interp-oper =  λ f x → tm-oper f (λ y → tm-var (transport-pow-𝒮 {oper-arity f} y))
           }



  -- The syntactic category "preserves" the equivalence of terms

  𝒮-respect-≈ : ∀ {Γ : Context} {u v : Term {Σ} Γ} → (Γ ⊢ u ≈ v) → (interp-term universalI u) ≈s (interp-term universalI v)
  𝒮-respect-≈ Theory.eq-refl = λ x → eq-refl
  𝒮-respect-≈ (Theory.eq-symm p) = symm-subst (𝒮-respect-≈ p)
  𝒮-respect-≈ (Theory.eq-tran p₁ p₂) = trans-subst (𝒮-respect-≈ p₁) (𝒮-respect-≈ p₂)
  𝒮-respect-≈ (Theory.eq-congr {Γ} {f} {xs} {ys} ps) =  Category.∘-resp-≈ 𝒮 {f = interp-oper universalI f} {h = interp-oper universalI f} {g = pow-tuple Σ cartesian-𝒮 (λ i → interp-term universalI (xs i))} {i = pow-tuple Σ cartesian-𝒮 (λ i → interp-term universalI (ys i))} (refl-subst) (pow-tuple-eq Σ cartesian-𝒮 (λ i x → 𝒮-respect-≈ (ps i) x))
  𝒮-respect-≈ (Theory.eq-axiom ε σ) = {!!}
  -- First attempt (didn't work) : λ x → eq-tran (𝒮-respect-subst (eq-lhs ε) σ x) (eq-symm (eq-tran (𝒮-respect-subst (eq-rhs ε) σ x) (eq-subst  (lift-subst σ) {u = (interp-term universalI (eq-rhs ε)) x} {v = (interp-term universalI (eq-lhs ε)) x} (𝒮-respect-≈ {u = (eq-rhs ε)} {v = (eq-lhs ε)} {!!} {!!}))))

  -- The universal model
  UniversalM : Model T universalI
  UniversalM = record { model-eq = λ ε x → equiv-subst (interp-term universalI (eq-lhs ε)) (interp-term universalI (eq-rhs ε)) (𝒮-respect-≈ {u = eq-lhs ε} {v = eq-rhs ε} (eq-id-action {ℓt} {Σ} {T} {Σ} (eq-axiom ε id-substitution))) (tm-var x) }

