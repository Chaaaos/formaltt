open import SingleSorted.AlgebraicTheory
open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module SingleSorted.Group where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)


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


-- some example terms
_ : Term {Σ} ctx-1
_ = tm-var var-var

y : Term {Σ} ctx-2
y = tm-var (var-inr var-var)

x : Term {Σ} ctx-2
x = tm-var (var-inr var-var)

_ : Term {Σ} ctx-2
_ = tm-oper mul (λ{ (var-inl x₁) → x ; (var-inr y₁) → y})


-- helper functions for creating terms
e' : ∀ {Γ : Context} → Term {Σ} Γ
e' {Γ} = tm-oper e λ()

inv' : ∀ {Γ : Context} → Term {Σ} Γ → Term {Σ} Γ
inv' x = tm-oper inv λ{ _ → x}

mul' : ∀ {Γ : Context} → Term {Σ} Γ → Term {Σ} Γ → Term {Σ} Γ
mul' x y = tm-oper mul λ{ (var-inl _) → x ; (var-inr _) → y}


x*y : Term {Σ} ctx-2
x*y = mul' x y

-- group equations
data GroupEq : Set where
  mul-assoc e-left e-right inv-left inv-right : GroupEq

-- concat-empty-idʳ : ctx-concat ctx-empty ctx-slot ≡ ctx-slot
-- concat-empty-idʳ = {!!}


𝒢 : Theory lzero Σ
𝒢 = record
  { eq = GroupEq
  ; eq-ctx = λ{ mul-assoc → ctx 3
                ; e-left → ctx 1
                ; e-right → ctx 1
                ; inv-left → ctx 1
                ; inv-right → ctx 1
              }
  ; eq-lhs = λ{ mul-assoc → mul' (mul' (tm-var (var-inl (var-inl (singleton-context (var-var)))))
                                        (tm-var (var-inl (var-inr var-var))))
                                 (tm-var (var-inr var-var))
                ; e-left → mul' e' (tm-var (singleton-context var-var))
                ; e-right → mul' (tm-var (singleton-context var-var)) e'
                ; inv-left → mul' (inv' (tm-var (singleton-context var-var)))
                                         (tm-var (singleton-context var-var))
                ; inv-right → mul' (tm-var (singleton-context var-var))
                                     (inv' (tm-var (singleton-context var-var)))
              }
  ; eq-rhs = λ{ mul-assoc → mul' (tm-var (var-inl (var-inl (singleton-context var-var))))
                                  (mul' (tm-var (var-inl (var-inr var-var)))
                                        (tm-var (var-inr var-var)))
                ; e-left → tm-var (singleton-context var-var)
                ; e-right → tm-var (singleton-context var-var)
                ; inv-left → e'
                ; inv-right → e'
              }
  }
  where
  singleton-context : (var ctx-slot) → var (ctx-concat ctx-empty ctx-slot)
  singleton-context (var-var) = var-inr var-var


_∗_ : ∀ {Γ} → Term {Σ} Γ → Term {Σ} Γ → Term {Σ} Γ
x ∗ y = mul' x y

_ⁱ : ∀ {Γ} → Term {Σ} Γ → Term {Σ} Γ
x ⁱ = inv' x

infixl 5 _∗_
infix 6 _ⁱ
