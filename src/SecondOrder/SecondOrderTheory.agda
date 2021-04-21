-- {-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Unary hiding (_∈_)
open import Data.Empty.Polymorphic
open import Data.List
open import Function.Base
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

import SecondOrder.Context as Context

module SecondOrder.SecondOrderTheory where

  -- Function extensionality
  postulate
    funext : ∀ {l l'} {X : Set l} {Y : X → Set l'} {f g : ∀ (x : X) → (Y x)} → (∀ (x : X) → ((f x) ≡ (g x))) → (f ≡ g)

  -- We work over a given notion of arity
  record Arity : Set₁ where
    field
      arity : Set -- the set of permissible arities, e.g., ℕ for finitary arities
      arg : arity → Set -- every arity gives a set of argument (position), e.g. Fin

  -- a second-order algebraic signature
  record Signature {ℓs ℓo ℓa} (𝔸 : Arity) : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
    open Arity 𝔸

    field
      sort : Set ℓs -- sorts
      oper : Set ℓo -- operations

    open Context sort public

    field
      oper-arity : oper → arity -- the arity of an operation
      oper-sort : oper → sort -- the operation sort
      arg-sort : ∀ (f : oper) → arg (oper-arity f) → sort -- the sorts of arguments
      arg-bind : ∀ (f : oper) → arg (oper-arity f) → Context -- the argument bindings

    -- the arguments of an operation
    oper-arg : oper → Set
    oper-arg f = arg (oper-arity f)

    -- a metavariable context
    record MetaContext : Set (lsuc ℓs) where
      field
        mv : Set ℓs -- the metavariables
        mv-arity : mv → Context -- the arity of a metavariable
        mv-sort : mv → sort -- the sort of a metavariable

    open MetaContext public

    -- infix 4 _∈ᴹ_

    mv-arg : ∀ (Θ : MetaContext) → mv Θ → sort → Set ℓs
    mv-arg Θ M A = A ∈ (mv-arity Θ M)

    ∅M : MetaContext
    ∅M = record
           { mv = ⊥
           ; mv-arity = ⊥-elim
           ; mv-sort = ⊥-elim
           }


    -- terms in a context of a given sort
    data Term (Θ : MetaContext) : ∀ (Γ : Context) (A : sort) → Set (lsuc (ℓa ⊔ ℓo ⊔ ℓs)) where
      tm-var : ∀ {Γ} {A} (x : A ∈ Γ) → Term Θ Γ A
      tm-meta : ∀ {Γ} (M : mv Θ) (ts : ∀ {B} (i : mv-arg Θ M B) → Term Θ Γ B) → Term Θ Γ (mv-sort Θ M)
      tm-oper : ∀ {Γ} (f : oper)
                  (es : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i)) →
                  Term Θ Γ (oper-sort f)

    -- Substitutions
    module _ {Θ : MetaContext} where

      infix 4 _⇒r_

      -- renaming
      _⇒r_ : ∀ (Γ Δ : Context) → Set ℓs
      Γ ⇒r Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

      -- extending a renaming
      extend-r : ∀ {Γ Δ} → Γ ⇒r Δ → ∀ {Ξ} → Γ ,, Ξ ⇒r Δ ,, Ξ
      extend-r ρ (var-inl x) = var-inl (ρ x)
      extend-r ρ (var-inr x) = var-inr x

      -- the identity renaming
      id-r : ∀ {Γ : Context} → Γ ⇒r Γ
      id-r x = x

      -- composition of renamings
      _∘r_ : ∀ {Γ Δ Θ : Context} → Δ ⇒r Θ → Γ ⇒r Δ → Γ ⇒r Θ
      (σ ∘r ρ) x = σ (ρ x)

      -- action of a renaming on terms
      tm-rename : ∀ {Γ Δ A} → Γ ⇒r Δ → Term Θ Γ A → Term Θ Δ A
      tm-rename ρ (tm-var x) = tm-var (ρ x)
      tm-rename ρ (tm-meta M ts) = tm-meta M (λ i → tm-rename ρ (ts i))
      tm-rename ρ (tm-oper f es) = tm-oper f (λ i → tm-rename (extend-r ρ) (es i))


      -- ∘r-tm-rename : ∀ {Γ Δ Ξ : Context} {A} (g :  Δ ⇒r Ξ) (f : Γ ⇒r Δ) (a : Term Θ Γ A) → tm-rename {A = A} (g ∘r f) a ≡ ((tm-rename g) ∘ (tm-rename f)) a
      -- ∘r-tm-rename g f (tm-var x) = refl
      -- ∘r-tm-rename g f (tm-meta M ts) = {!!}
      -- ∘r-tm-rename g f (tm-oper f₁ es) = {!!}

      -- id-r-tm-rename : ∀ {Γ A} (a : Term Θ Γ A) → (tm-rename {A = A} id-r) a ≡ a
      -- id-r-tm-rename (tm-var x) = refl
      -- id-r-tm-rename (tm-meta M ts) = Relation.Binary.PropositionalEquality.cong (tm-meta M) {!!}
      -- id-r-tm-rename (tm-oper f es) = Relation.Binary.PropositionalEquality.cong (tm-oper f) {!!}

      weakenˡ : ∀ {Γ Δ A} → Term Θ Γ A → Term Θ (Γ ,, Δ) A
      weakenˡ = tm-rename var-inl

      weakenʳ : ∀ {Γ Δ A} → Term Θ Δ A → Term Θ (Γ ,, Δ) A
      weakenʳ = tm-rename var-inr

      -- substitition
      _⇒s_ : ∀ (Γ Δ : Context) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
      Γ ⇒s Δ = ∀ {A} (x : A ∈ Δ) → Term Θ Γ A

      infix 4 _⇒s_

      -- extending a substitution
      extend-sˡ : ∀ {Γ Δ Ξ} → Γ ⇒s Δ → Γ ,, Ξ ⇒s Δ ,, Ξ
      extend-sˡ {Ξ = Ξ} σ (var-inl x) = weakenˡ (σ x)
      extend-sˡ σ (var-inr x) = tm-var (var-inr x)

      extend-sʳ : ∀ {Γ Δ Ξ} → Γ ⇒s Δ → Ξ ,, Γ ⇒s Ξ ,, Δ
      extend-sʳ {Ξ = Ξ} σ (var-inl x) = tm-var (var-inl x)
      extend-sʳ σ (var-inr x) = weakenʳ (σ x)

      -- the action of a substitution on a term (contravariant)
      _[_]s : ∀ {Γ Δ : Context} {A : sort} → Term Θ Δ A → Γ ⇒s Δ → Term Θ Γ A
      (tm-var x) [ σ ]s = σ x
      (tm-meta M ts) [ σ ]s = tm-meta M (λ i → (ts i) [ σ ]s)
      (tm-oper f es) [ σ ]s = tm-oper f (λ i → es i [ extend-sˡ σ ]s)

      infixr 6 _[_]s

      -- identity substitution
      id-s : ∀ {Γ : Context} → Γ ⇒s Γ
      id-s = tm-var

      -- composition of substitutions
      _∘s_ : ∀ {Γ Δ Θ : Context} → Δ ⇒s Θ → Γ ⇒s Δ → Γ ⇒s Θ
      (σ ∘s ρ) x = σ x [ ρ ]s

      infixl 7 _∘s_

  module _ {ℓs ℓo ℓa} {𝔸 : Arity}  {Σ : Signature {ℓs} {ℓo} {ℓa} 𝔸} where
    open Signature Σ

    -- metavariable instantiation
    mv-inst  : MetaContext → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa))
    mv-inst Θ = ∀ {M : mv Θ} → Term ∅M (mv-arity Θ M) (mv-sort Θ M)
    -- this definition of metavariable extension is different from the one of the paper : here all the meta-variable are instatiated at once (I should change this) and replaced by terms without metavariables (so composing instatiations doesn't make sense for the moment)

    -- action of a metavariable instatiation on terms
    _[_]M : ∀ {Γ : Context} {A : sort} {Θ : MetaContext} → Term Θ Γ A → mv-inst Θ → Term ∅M Γ A
    (tm-var x) [ ι ]M = tm-var x
    (tm-meta M ts) [ ι ]M = ι [ (λ i → ts i [ ι ]M) ]s
    (tm-oper f es) [ ι ]M = tm-oper f (λ i → es i [ ι ]M)

    infixr 6 _[_]M

    --  equations (based on the jugements in "A general definitipn of dependent type theories")
    record Equation : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
      constructor make-eq
      field
        eq-mv-ctx : MetaContext -- metavariable context of an equation
        eq-ctx : Context -- variable context of an equation
        eq-sort : sort -- sort of an equation
        eq-lhs : Term eq-mv-ctx eq-ctx eq-sort -- left-hand side
        eq-rhs : Term eq-mv-ctx eq-ctx eq-sort -- right-hand side

    infix 5 make-eq

    syntax make-eq Θ Γ A s t = Θ ⊕ Γ ∥ s ≈ t ⦂ A

    -- Theory
    -- an equational theory is a family of axioms over a given sort
    record Theory ℓ  : Set (lsuc (ℓ ⊔ ℓs ⊔ ℓo ⊔ ℓa)) where
      field
        ax : Set ℓ -- the axioms
        ax-eq : ax → Equation

      ax-ctx : ax → Context
      ax-ctx ε = Equation.eq-ctx (ax-eq ε)

      ax-mv-ctx : ax → MetaContext
      ax-mv-ctx ε = Equation.eq-mv-ctx (ax-eq ε)

      ax-sort : ax → sort
      ax-sort ε = Equation.eq-sort (ax-eq ε)

      ax-lhs : ∀ (ε : ax) → Term (ax-mv-ctx ε) (ax-ctx ε) (ax-sort ε)
      ax-lhs ε = Equation.eq-lhs (ax-eq ε)

      ax-rhs : ∀ (ε : ax) → Term (ax-mv-ctx ε) (ax-ctx ε) (ax-sort ε)
      ax-rhs ε = Equation.eq-rhs (ax-eq ε)

      -- equality of terms
      infix 4 ⊢_

      data ⊢_ : Equation → Set (lsuc (ℓ ⊔ ℓs ⊔ ℓo ⊔ ℓa)) where
        -- general rules
        eq-refl : ∀ {Θ Γ A} {t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ t ≈ t ⦂ A
        eq-symm : ∀ {Θ Γ A} {s t : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Γ ∥ t ≈ s ⦂ A
        eq-tran : ∀ {Θ Γ A} {s t u : Term Θ Γ A} → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Γ ∥ t ≈ u ⦂ A → ⊢ Θ ⊕ Γ ∥ s ≈ u ⦂ A
        -- congruence rule for operations
        eq-congr : ∀ {Γ Θ} {f : oper} {xs ys : ∀ (i : oper-arg f) → Term Θ (Γ ,, arg-bind f i) (arg-sort f i)} →
                 (∀ i → ⊢ Θ ⊕ (Γ ,, arg-bind f i) ∥ (xs i) ≈ (ys i) ⦂ (arg-sort f i)) → ⊢ Θ ⊕ Γ ∥  (tm-oper f xs) ≈ (tm-oper f ys) ⦂ (oper-sort f)
        -- congruence rule for metavariables
        eq-congr-mv : ∀ {Γ Θ} {M : mv Θ} {xs ys : ∀ {B : sort} (i : mv-arg Θ M B) → Term Θ Γ B} →
                 (∀ {B : sort} (i : mv-arg Θ M B) → ⊢ Θ ⊕ Γ ∥ (xs i) ≈ (ys i) ⦂ B) → ⊢ Θ ⊕ Γ ∥  (tm-meta M xs) ≈ (tm-meta M ys) ⦂ (mv-sort Θ M)
        -- equational axiom
        eq-axiom : ∀ (ε : ax) {Γ : Context} (σ : Γ ⇒s ax-ctx ε) →
                   ⊢ (ax-mv-ctx ε) ⊕ Γ ∥ (ax-lhs ε [ σ ]s) ≈ (ax-rhs ε [ σ ]s) ⦂ (ax-sort ε)

      _≈s_ : ∀ {Γ Δ : Context} {Θ} (σ τ : Δ ⇒s Γ) → Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa ⊔ ℓ))
      _≈s_ {Γ} {Δ} {Θ} σ τ = ∀ {A} (x : A ∈ Γ) → ⊢ Θ ⊕ Δ ∥ σ x ≈ τ x ⦂ A

      -- terms and judgemental equality form a setoid
      eq-setoid : ∀ (Γ : Context) (Θ : MetaContext) (A : sort) → Setoid (lsuc (ℓo ⊔ ℓs ⊔ ℓa )) (lsuc (ℓ ⊔ ℓo ⊔ ℓs ⊔ ℓa))
      eq-setoid Γ Θ A =
        record
          { Carrier = Term Θ Γ A
          ;  _≈_ = λ s t → (⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A)
          ; isEquivalence =
                          record
                            { refl = eq-refl
                            ; sym = eq-symm
                            ; trans = eq-tran
            }
          }


      -- extension of substitutions preserve equality
      id-s-extendˡ : ∀ {Θ Γ Ξ A} {a : A ∈ (Γ ,, Ξ)} → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ extend-sˡ {Θ} {Γ} {Γ} {Ξ} (id-s {Γ = Γ}) {A} a ≈  id-s {Γ = Γ ,, Ξ} a ⦂ A
      id-s-extendˡ {a = Context.var-inl a} = eq-refl
      id-s-extendˡ {a = Context.var-inr a} = eq-refl

      -- enables to use a renaming as a substitution
      r-to-subst : ∀ {Θ Γ Δ A} (ρ : _⇒r_ {Θ} Γ Δ) → _⇒s_ {Θ} Δ Γ
      r-to-subst ρ x = tm-var (ρ x)

      r-to-subst-≈ :  ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {ρ : _⇒r_ {Θ} Γ Δ} → ⊢ Θ ⊕ Δ ∥ (tm-rename ρ t) ≈ t [ (r-to-subst {A = A} ρ) ]s ⦂ A
      r-to-subst-≈ {t = Signature.tm-var x} = eq-refl
      r-to-subst-≈ {t = Signature.tm-meta M ts} = eq-congr-mv λ i → r-to-subst-≈
      r-to-subst-≈ {t = Signature.tm-oper f es} = eq-congr λ i → {!!}

      -- renaming preserves equality of terms
      ≈tm-rename : ∀ {Θ Γ Δ A} {s t : Term Θ Γ A} {ρ : _⇒r_ {Θ} Γ Δ} → ⊢ Θ ⊕ Γ ∥ s ≈ t ⦂ A → ⊢ Θ ⊕ Δ ∥ tm-rename ρ s ≈ tm-rename ρ t ⦂ A
      ≈tm-rename eq-refl = eq-refl
      ≈tm-rename (eq-symm p) = eq-symm (≈tm-rename p)
      ≈tm-rename (eq-tran p₁ p₂) = eq-tran (≈tm-rename p₁) (≈tm-rename p₂)
      ≈tm-rename (eq-congr p) = eq-congr λ i → ≈tm-rename (p i)
      ≈tm-rename (eq-congr-mv p) = eq-congr-mv λ i → ≈tm-rename (p i)
      ≈tm-rename (eq-axiom ε σ) = {!!}

      -- weakening preserves equality of substitutions
      ≈s-weakenˡ : ∀ {Θ Γ Δ Ξ A} {σ τ : Δ ⇒s Γ} {x : A ∈ Γ} → σ ≈s τ → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ weakenˡ (σ x) ≈ weakenˡ (τ x) ⦂ A
      ≈s-weakenˡ {x = x} p = ≈tm-rename (p x)

      -- extension of substitutions preserves equality of substitutions
      ≈s-extend-sˡ : ∀ {Θ Γ Δ Ξ} {σ τ : Γ ⇒s Δ} → σ ≈s τ → extend-sˡ {Θ} {Γ} {Δ} {Ξ} σ ≈s extend-sˡ {Θ} {Γ} {Δ} {Ξ} τ
      ≈s-extend-sˡ p (Context.var-inl x) = ≈s-weakenˡ p
      ≈s-extend-sˡ p (Context.var-inr x) = eq-refl

      -- actions of equal substitutions are pointwise equal
      subst-congr : ∀ {Θ Γ Δ A} {t : Term Θ Γ A} {σ τ : Δ ⇒s Γ} → σ ≈s τ → ⊢ Θ ⊕ Δ ∥ t [ σ ]s ≈  t [ τ ]s ⦂ A
      subst-congr {t = Signature.tm-var x} p = p x
      subst-congr {t = Signature.tm-meta M ts} p = eq-congr-mv λ i → subst-congr {t = ts i} p
      subst-congr {t = Signature.tm-oper f es} p = eq-congr λ i → subst-congr-aux {t = es i} p
        where
          subst-congr-aux : ∀ {Θ Γ Δ Ξ A} {t : Term Θ (Γ ,, Ξ) A} {σ τ : Δ ⇒s Γ} → σ ≈s τ → ⊢ Θ ⊕ (Δ ,, Ξ) ∥ t [ extend-sˡ σ ]s ≈  t [ extend-sˡ τ ]s ⦂ A
          subst-congr-aux {Γ = Γ} {Ξ = Ξ} {t = t} p = subst-congr {Γ = Γ ,, Ξ} {t = t} λ x → ≈s-extend-sˡ p x


      -- the action of the identity substitution is the identity
      id-action : ∀ {Θ Γ A} {a : Term Θ Γ A} → (⊢ Θ ⊕ Γ ∥ a ≈ (a [ id-s ]s) ⦂ A)
      id-action {a = Signature.tm-var x} = eq-refl
      id-action {a = Signature.tm-meta M ts} = eq-congr-mv λ i → id-action
      id-action {a = Signature.tm-oper f es} = eq-congr λ i → eq-tran id-action-aux (eq-symm (subst-congr {t = es i} λ x → id-s-extendˡ))
        where
          id-action-aux : ∀ {Θ Γ Ξ A} {t : Term Θ (Γ ,, Ξ) A} → ⊢ Θ ⊕ (Γ ,, Ξ) ∥ t ≈  (t [ id-s ]s) ⦂ A
          id-action-aux = id-action

      eq-axiom-id : ∀ (ε : ax) → ⊢ ((ax-mv-ctx ε) ⊕ ax-ctx ε ∥ ax-lhs ε ≈ ax-rhs ε ⦂  (ax-sort ε))
      eq-axiom-id ε = eq-tran id-action (eq-tran (eq-axiom ε id-s) (eq-symm id-action))

