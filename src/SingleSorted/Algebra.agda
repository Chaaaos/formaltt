open import Agda.Primitive
open import Agda.Builtin.Nat
open import Data.Fin

open import Experimental.Equality

open import Categories.Category
open import Categories.Category.Cartesian

module Experimental.SingleSortedAlgebra where

-- an algebraic signature
record Signature : Set₁ where
  field
    oper : Set -- operations
    oper-arity : oper → Nat -- the arity of an operation

open Signature

Context = Nat
var = Fin

-- terms over a signature in a context of a given sort
data Term (Σ : Signature) (Γ : Context) : Set where
  tm-var : ∀ (x : var Γ) → Term Σ Γ
  tm-op : ∀ (f : oper Σ) → (∀ (i : Fin (oper-arity Σ f)) → Term Σ Γ) → Term Σ Γ

substitution : ∀ (Σ : Signature) (Γ Δ : Context) → Set
substitution Σ Γ Δ = var Γ → Term Σ Δ

-- identity substitution
id-substitution : ∀ {Σ : Signature} {Γ : Context} → substitution Σ Γ Γ
id-substitution = tm-var

-- the action of a substitution on a term
_·_ : ∀ {Σ : Signature} {Γ Δ : Context} → substitution Σ Γ Δ → Term Σ Γ → Term Σ Δ
σ · (tm-var x) = σ x
σ · (tm-op f x) = tm-op f (λ i → σ · x i)

infixr 6 _·_

-- composition of substitutions
_∘s_ : ∀ {Σ : Signature} {Γ Δ Θ : Context} → substitution Σ Δ Θ → substitution Σ Γ Δ → substitution Σ Γ Θ
(σ ∘s τ) x = σ · τ x

infixl 7 _∘s_

-- an equational theory is a family of equations over a given sort
record Theory ℓ (Σ : Signature) : Set (lsuc ℓ) where
  field
    eq : Set ℓ
    eq-ctx : ∀ (ε : eq) → Context
    eq-lhs : ∀ (ε : eq) → Term Σ (eq-ctx ε)
    eq-rhs : ∀ (ε : eq) → Term Σ (eq-ctx ε)

  infix 4 _⊢_≈_

  -- equality of terms
  data _⊢_≈_ : (Γ : Context) → Term Σ Γ → Term Σ Γ → Set (lsuc ℓ) where
    -- general rules
    eq-refl : ∀ {Γ} {t : Term Σ Γ} → Γ ⊢ t ≈ t
    eq-symm : ∀ {Γ} {s t : Term Σ Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ s
    eq-tran : ∀ {Γ} {s t u : Term Σ Γ} → Γ ⊢ s ≈ t → Γ ⊢ t ≈ u → Γ ⊢ s ≈ u
    -- congruence rule
    eq-congr : ∀ {Γ} {f : oper Σ} (x y : ∀ (i : Fin (oper-arity Σ f)) → Term Σ Γ) →
               (∀ i → Γ ⊢ x i ≈ y i) → Γ ⊢ tm-op f x ≈ tm-op f y
    -- equational axiom
    eq-axiom : ∀ (ε : eq) {Δ : Context} (σ : substitution Σ (eq-ctx ε) Δ) →
               Δ ⊢ σ · (eq-lhs ε) ≈ σ · eq-rhs ε

  -- equality of substitutions
  _≈s_ : ∀ {Γ Δ : Context} → substitution Σ Γ Δ → substitution Σ Γ Δ → Set (lsuc ℓ)
  _≈s_ {Δ = Δ} σ ρ = ∀ x → Δ ⊢ σ x ≈ ρ x

  -- composition of substitutions is functorial
  subst-∘s : ∀ {Γ Δ Θ} (σ : substitution Σ Δ Θ) (τ : substitution Σ Γ Δ) → ∀ (t : Term Σ Γ) → Θ ⊢ (σ · τ · t) ≈ (σ ∘s τ · t)
  subst-∘s σ τ (tm-var x) = eq-refl
  subst-∘s σ τ (tm-op f x) = eq-congr (λ i → σ · τ · x i) (λ i → σ ∘s τ · x i) λ i → subst-∘s σ τ (x i)

  -- substitution preserves equality
  eq-subst : ∀ {Γ Δ : Context} (σ : substitution Σ Γ Δ) {s t : Term Σ Γ} → Γ ⊢ s ≈ t → Δ ⊢ σ · s ≈ σ · t
  eq-subst σ eq-refl = eq-refl
  eq-subst σ (eq-symm ξ) = eq-symm (eq-subst σ ξ)
  eq-subst σ (eq-tran ζ ξ) = eq-tran (eq-subst σ ζ) (eq-subst σ ξ)
  eq-subst σ (eq-congr x y ξ) = eq-congr (λ i → σ · x i) (λ i → σ · y i) λ i → eq-subst σ (ξ i)
  eq-subst σ (eq-axiom ε τ) =
    eq-tran (subst-∘s σ τ (eq-lhs ε))
            (eq-tran (eq-axiom ε (σ ∘s τ)) (eq-symm (subst-∘s σ τ (eq-rhs ε))))

module _ {ℓt o ℓ e : Level}
         (Σ : Signature) (T : Theory ℓt Σ) (𝒞 : Category o ℓ e)
         (cartesian-𝒞 : Cartesian 𝒞) where
  open Category 𝒞
  open import Categories.Object.Product 𝒞
  open Cartesian cartesian-𝒞
  open HomReasoning

  -- We use our own definition of powers (because the one in the library has a silly special case n = 1
  pow : ∀ (A : Obj) (n : Nat) → Obj
  pow A zero = ⊤
  pow A (suc n) = pow A n × A

  pow-π : ∀ {A : Obj} {n : Nat} (i : Fin n) → pow A n ⇒ A
  pow-π {_} {suc n} zero = π₂
  pow-π {_} {suc n} (suc i) = (pow-π i) ∘ π₁

  pow-tuple : ∀ {A B : Obj} {n : Nat} → (Fin n → A ⇒ B) → A ⇒ pow B n
  pow-tuple {n = zero} fs = !
  pow-tuple {n = suc n} fs = ⟨ (pow-tuple (λ i → fs (suc i))) , (fs zero) ⟩

  pow-tuple-∘ : ∀ {A B C : Obj} {n : Nat} {fs : Fin n → B ⇒ C} {g : A ⇒ B} →
                pow-tuple (λ i → fs i ∘ g) ≈ pow-tuple fs ∘ g
  pow-tuple-∘ {n = zero} {fs} {g} = !-unique (! ∘ g)
  pow-tuple-∘ {n = suc n} {fs = fs} =
    let open product in
      (⟨⟩-congʳ (pow-tuple-∘ {fs = λ i → fs (suc i)})) ○ (⟺ ⟨⟩∘)

  pow-tuple-id : ∀ {A : Obj} {n} → pow-tuple {A = pow A n} {n = n} pow-π ≈ id
  pow-tuple-id {n = zero} = !-unique id
  pow-tuple-id {n = suc n} = (⟨⟩-congʳ ((pow-tuple-∘ {n = n}) ○ ((pow-tuple-id {n = n} ⟩∘⟨refl) ○ identityˡ))) ○ η

  -- An interpretation of Σ in 𝒞
  record Interp : Set (o ⊔ ℓ ⊔ e) where
    field
      interp-carrier : Obj
      interp-oper : ∀ (f : oper Σ) → pow interp-carrier (oper-arity Σ f) ⇒ interp-carrier

    -- the interpretation of a term
    interp-term : ∀ {Γ : Context} → Term Σ Γ →  𝒞 [ (pow interp-carrier Γ) , interp-carrier ]
    interp-term (tm-var x) = pow-π x
    interp-term (tm-op f ts) = 𝒞 [ interp-oper f ∘ pow-tuple (λ i → interp-term (ts i)) ]

  -- Every signature has the trivial interpretation

  TrivialInterp : Interp
  TrivialInterp = record { interp-carrier = ⊤ ; interp-oper = λ f → ! }

  record Hom (A B : Interp) : Set (o ⊔ ℓ ⊔ e) where
    open Interp

    field
      hom-morphism : interp-carrier A  ⇒ interp-carrier B
      hom-commute :
         ∀ (f : oper Σ) →
         hom-morphism ∘ interp-oper A f ≈
             interp-oper B f ∘ pow-tuple {n = oper-arity Σ f} (λ i →  hom-morphism ∘  interp-oper A f)

  -- The identity homomorphism
  Id : ∀ (A : Interp) → Hom A A
  Id A = record
          { hom-morphism = id
          ; hom-commute = {!!}
          }

  -- Compositon of homomorphisms
  _∘I_ : ∀ {A B C : Interp} → Hom B C → Hom A B → Hom A C
  ϕ ∘I ψ =
    let open Hom in
    record { hom-morphism = (hom-morphism ϕ) ∘ (hom-morphism ψ)
           ; hom-commute = {!!} }

  -- Model of a theory
  record Mod : Set (ℓt ⊔ o ⊔ ℓ ⊔ e) where
    open Interp
    open Theory

    field
      {{model-interp}} : Interp
      model-eq : ∀ (ε : eq T) → interp-term model-interp (eq-lhs T ε) ≈ interp-term model-interp (eq-rhs T ε)

  -- Every theory has the trivial model, whose carrier is the terminal object

  TrivialModel : Mod
  TrivialModel =
    record
      { model-interp = TrivialInterp
      ; model-eq = λ ε → !-unique₂
      }

  -- Syntactic category
  SynCat : Category lzero lzero (lsuc ℓt)
  SynCat =
    let open Theory in
      record
        { Obj = Context
        ; _⇒_ = substitution Σ
        ; _≈_ = _≈s_ T
        ; id =  id-substitution
        ; _∘_ =  _∘s_
        ; assoc = {!!}
        ; sym-assoc = {!!}
        ; identityˡ = {!!}
        ; identityʳ = {!!}
        ; identity² = {!!}
        ; equiv = {!!}
        ; ∘-resp-≈ = {!!}
        }
