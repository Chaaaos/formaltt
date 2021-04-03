open import SingleSorted.AlgebraicTheory
open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SingleSorted.Substitution
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

module SingleSorted.Group where

data GroupOp : Set where
  e : GroupOp
  inv : GroupOp
  mul : GroupOp

_ : Context
_ = ctx-empty

_ : Context
_ = ctx-concat ctx-slot ctx-empty

_ : var ctx-slot
_ = var-var

_ : var (ctx-concat ctx-slot ctx-slot)
_ = var-inl var-var

_ : var (ctx-concat ctx-slot ctx-slot)
_ = var-inr var-var

ctx-1 : Context
ctx-1 = ctx-slot

ctx-2 : Context
ctx-2 = ctx-concat ctx-1 ctx-1

ctx : ∀ (n : ℕ) → Context
ctx zero = ctx-empty
ctx (suc n) = ctx-concat (ctx n) ctx-slot

-- the signature of the theory of groups
-- has one constant, one unary operation, one binary operation
Σ : Signature
Σ = record { oper = GroupOp ; oper-arity = λ{ e → ctx-empty ; inv → ctx 1 ; mul → ctx 2} }

open Signature Σ

-- some example terms
_ : Term ctx-1
_ = tm-var var-var

_ : Term ctx-2
_ = tm-var (var-inr var-var)

_ : Term ctx-2
_ = tm-var (var-inr var-var)


-- helper functions for creating terms
e' : ∀ {Γ : Context} → Term Γ
e' {Γ} = tm-oper e λ()

-- inv' : ∀ {Γ : Context} → Term Γ → Term Γ
-- inv' x = tm-oper inv λ{ _ → x}

-- mul' : ∀ {Γ : Context} → Term Γ → Term Γ → Term Γ
-- mul' x y = tm-oper mul λ{ (var-inl _) → x ; (var-inr _) → y}

concat-empty : var (ctx-concat ctx-empty ctx-slot) → (var ctx-slot)
concat-empty (var-inr x) = x


x*y : Term ctx-2
x*y = tm-oper mul λ{ (var-inl x) → tm-var (var-inl (concat-empty x)) ; (var-inr y) → tm-var (var-inr y)}

-- concat-empty-idʳ : ctx-concat ctx-empty ctx-slot ≡ ctx-slot
-- concat-empty-idʳ = {!!}

singleton-context : (var ctx-slot) → var (ctx-concat ctx-empty ctx-slot)
singleton-context (var-var) = var-inr var-var

σ : ∀ {Γ : Context} {t : Term Γ} →  Γ ⇒s (ctx 1)
σ {Γ} {t} = λ{ (var-inr var-var) → t}

δ : ∀ {Γ : Context} {t : Term Γ} {s : Term Γ} →   Γ ⇒s (ctx 2)
δ {Γ} {t} {s} = λ{ (var-inl x) → t ; (var-inr y) → s}

_∗_ : ∀ {Γ} → Term Γ → Term Γ → Term Γ
t ∗ s =  tm-oper mul λ{ xs → δ {t = t} {s = s} xs}

_ⁱ : ∀ {Γ : Context} →  Term Γ → Term Γ
t ⁱ =  tm-oper inv λ{ x → σ {t = t} x}

-- _∗_ : ∀ {Γ} → Term Γ → Term Γ → Term Γ
-- t ∗ s =  tm-oper mul λ{ (var-inl x) → t ; (var-inr args) → s}

-- _ⁱ : ∀ {Γ : Context} →  Term Γ → Term Γ
-- t ⁱ =  tm-oper inv λ{ x → t }

infixl 5 _∗_
infix 6 _ⁱ

_ : Term (ctx 2)
_ = tm-var (var-inl (var-inr var-var)) ∗ tm-var (var-inr var-var)

_ : Term (ctx 1)
_ = e' ∗ a
  where
  a : Term (ctx 1)
  a = tm-var (var-inr var-var)

-- group equations
data GroupEq : Set where
  mul-assoc e-left e-right inv-left inv-right : GroupEq

mul-assoc-ax : Equation
e-left-ax : Equation
e-right-ax : Equation
inv-left-ax : Equation
inv-right-ax : Equation

mul-assoc-ax = record { eq-ctx = ctx 3
                      ; eq-lhs = x ∗ y ∗ z
                      ; eq-rhs = x ∗ (y ∗ z)
                      }
             where
             x : Term (ctx 3)
             y : Term (ctx 3)
             z : Term (ctx 3)
             x = tm-var (var-inl (var-inl (var-inr var-var)))
             y = tm-var (var-inl (var-inr var-var))
             z = tm-var (var-inr var-var)

e-left-ax = record { eq-ctx = ctx 1 ; eq-lhs = e' ∗ x ; eq-rhs = x }
  where
  x : Term (ctx 1)
  x = tm-var (var-inr var-var)

e-right-ax = record { eq-ctx = ctx 1 ; eq-lhs = x ∗ e' ; eq-rhs = x }
  where
  x : Term (ctx 1)
  x = tm-var (var-inr var-var)


inv-left-ax = record { eq-ctx = ctx 1 ; eq-lhs = x ⁱ ∗ x ; eq-rhs = e' }
  where
  x : Term (ctx 1)
  x = tm-var (var-inr var-var)

inv-right-ax = record { eq-ctx = ctx 1 ; eq-lhs = x ∗ x ⁱ ; eq-rhs = e' }
  where
  x : Term (ctx 1)
  x = tm-var (var-inr var-var)


𝒢 : Theory lzero Σ
𝒢 = record { ax = GroupEq
            ; ax-eq = λ{ mul-assoc → mul-assoc-ax
                       ; e-left → e-left-ax
                       ; e-right → e-right-ax
                       ; inv-left → inv-left-ax
                       ; inv-right → inv-right-ax
                       }
            }
