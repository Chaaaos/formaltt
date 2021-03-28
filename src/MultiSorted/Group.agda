open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SingleSorted.Substitution
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
import MultiSorted.Context as Context 

module MultiSorted.Group where

data 𝒜 : Set₀ where
  A : 𝒜

single-sort : ∀ (X : 𝒜) → X ≡ A
single-sort A = refl

open import MultiSorted.AlgebraicTheory

open import MultiSorted.AlgebraicTheory
data GroupOp : Set where
  e : GroupOp
  inv : GroupOp
  mul : GroupOp

ctx : ∀ (n : ℕ) → Context.Context 𝒜
ctx zero = Context.ctx-empty
ctx (suc n) = Context.ctx-concat (ctx n) (Context.ctx-slot A)

-- the signature of the theory of small groups
-- has one constant, one unary operation, one binary operation
Σ : Signature {lzero} {lzero}
Σ = record { sort = 𝒜
           ; oper = GroupOp
           ; oper-arity = λ{ e → ctx 0 ; inv → ctx 1 ; mul → ctx 2}
           ; oper-sort = λ{ e → A ; inv → A ; mul → A}
           }

open Signature Σ

singleton-context : (var (ctx-slot A)) → var (ctx-concat ctx-empty (ctx-slot A))
singleton-context (var-var {A}) = var-inr (var-var {A})

single-sort-context : ∀ {Γ : Context} (x : var Γ) → sort-of Γ x ≡ A
single-sort-context {Γ} x = single-sort (Context.sort-of 𝒜  Γ x)

single-sort-terms : ∀ {X : 𝒜} {Γ : Context} → Term Γ X ≡ Term Γ A
single-sort-terms {A} = refl

σ : ∀ {Γ : Context} {t : Term Γ A} →  Γ ⇒s (ctx 1)
σ {Γ} {t} = λ{ (var-inr var-var) → t}

δ : ∀ {Γ : Context} {t : Term Γ A} {s : Term Γ A} → Γ ⇒s (ctx 2)
δ {Γ} {t} {s} = sub
  where
  sub : Γ ⇒s (ctx 2)
  sub (var-inl x) rewrite (single-sort-terms {(sort-of (ctx 2) (var-inl x))} {Γ}) = t
  sub (var-inr y) rewrite (single-sort-terms {(sort-of (ctx 2) (var-inr y))} {Γ}) = s

-- helper functions for creating terms
e' : ∀ {Γ : Context} → Term Γ A
e' {Γ} = tm-oper e λ()

_∗_ : ∀ {Γ} → Term Γ A → Term Γ A → Term Γ A
t ∗ s =  tm-oper mul λ{ xs → δ {t = t} {s = s} xs}

_ⁱ : ∀ {Γ : Context} →  Term Γ A → Term Γ A
t ⁱ =  tm-oper inv λ{ x → σ {t = t} x}

-- _∗_ : ∀ {Γ} → Term Γ A → Term Γ A → Term Γ A
-- _∗_ {Γ} t s  =  tm-oper mul λ{ (var-inl i) → {!!} ; (var-inr i) → {!!}}

-- _ⁱ : ∀ {Γ : Context} →  Term Γ A → Term Γ A
-- t ⁱ =  tm-oper inv λ{ x → t }

infixl 5 _∗_
infix 6 _ⁱ

_ : Term (ctx 2) A
_ = tm-var (var-inl (var-inr var-var)) ∗ tm-var (var-inr var-var)


-- group equations
data GroupEq : Set where
  mul-assoc e-left e-right inv-left inv-right : GroupEq

mul-assoc-eq : Equation Σ
e-left-eq : Equation Σ
e-right-eq : Equation Σ
inv-left-eq : Equation Σ
inv-right-eq : Equation Σ

mul-assoc-eq = record { eq-ctx = ctx 3
                      ; eq-lhs = x ∗ y ∗ z
                      ; eq-rhs = x ∗ (y ∗ z)
                      }
             where
             x : Term (ctx 3) A
             y : Term (ctx 3) A
             z : Term (ctx 3) A
             x = tm-var (var-inl (var-inl (var-inr var-var)))
             y = tm-var (var-inl (var-inr var-var))
             z = tm-var (var-inr var-var)

e-left-eq = record { eq-ctx = ctx 1 ; eq-lhs = e' ∗ x ; eq-rhs = x }
  where
  x : Term (ctx 1) A
  x = tm-var (var-inr var-var)

e-right-eq = record { eq-ctx = ctx 1 ; eq-lhs = x ∗ e' ; eq-rhs = x }
  where
  x : Term (ctx 1) A
  x = tm-var (var-inr var-var)


inv-left-eq = record { eq-ctx = ctx 1 ; eq-lhs = x ⁱ ∗ x ; eq-rhs = e' }
  where
  x : Term (ctx 1) A
  x = tm-var (var-inr var-var)

inv-right-eq = record { eq-ctx = ctx 1 ; eq-lhs = x ∗ x ⁱ ; eq-rhs = e' }
  where
  x : Term (ctx 1) A
  x = tm-var (var-inr var-var)


𝒢 : Theory lzero Σ
𝒢 = record { ax = GroupEq
            ; ax-eq = λ{ mul-assoc → mul-assoc-eq
                       ; e-left → e-left-eq
                       ; e-right → e-right-eq
                       ; inv-left → inv-left-eq
                       ; inv-right → inv-right-eq
                       }
            }
