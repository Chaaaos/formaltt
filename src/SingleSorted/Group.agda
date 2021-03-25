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

_ : Term {Σ} ctx-2
_ = tm-var (var-inr var-var)

_ : Term {Σ} ctx-2
_ = tm-var (var-inr var-var)


-- helper functions for creating terms
e' : ∀ {Γ : Context} → Term {Σ} Γ
e' {Γ} = tm-oper e λ()

-- inv' : ∀ {Γ : Context} → Term {Σ} Γ → Term {Σ} Γ
-- inv' x = tm-oper inv λ{ _ → x}

-- mul' : ∀ {Γ : Context} → Term {Σ} Γ → Term {Σ} Γ → Term {Σ} Γ
-- mul' x y = tm-oper mul λ{ (var-inl _) → x ; (var-inr _) → y}

concat-empty : var (ctx-concat ctx-empty ctx-slot) → (var ctx-slot)
concat-empty (var-inr x) = x


x*y : Term {Σ} ctx-2
x*y = tm-oper mul λ{ (var-inl x) → tm-var (var-inl (concat-empty x)) ; (var-inr y) → tm-var (var-inr y)}

-- group equations
data GroupEq : Set where
  mul-assoc e-left e-right inv-left inv-right : GroupEq

-- concat-empty-idʳ : ctx-concat ctx-empty ctx-slot ≡ ctx-slot
-- concat-empty-idʳ = {!!}

singleton-context : (var ctx-slot) → var (ctx-concat ctx-empty ctx-slot)
singleton-context (var-var) = var-inr var-var

σ : ∀ {Γ : Context} {t : Term {Σ} Γ} →  substitution Σ Γ (ctx 1)
σ {Γ} {t} = λ{ (var-inr var-var) → t}

δ : ∀ {Γ : Context} {t : Term {Σ} Γ} {s : Term {Σ} Γ} →  substitution Σ Γ (ctx 2)
δ {Γ} {t} {s} = λ{ (var-inl x) → t ; (var-inr y) → s}

_∗_ : ∀ {Γ} → Term {Σ} Γ → Term {Σ} Γ → Term {Σ} Γ
t ∗ s =  tm-oper mul λ{ xs → δ {t = t} {s = s} xs}

_ⁱ : ∀ {Γ : Context} →  Term {Σ} Γ → Term {Σ} Γ
t ⁱ =  tm-oper inv λ{ x → σ {t = t} x}

infixl 5 _∗_
infix 6 _ⁱ

_ : Term {Σ} (ctx 2)
_ = tm-var (var-inl (var-inr var-var)) ∗ tm-var (var-inr var-var)

𝒢 : Theory lzero Σ
𝒢 = record
  { eq = GroupEq
  ; eq-ctx = λ{ mul-assoc → ctx 3
                ; e-left → ctx 1
                ; e-right → ctx 1
                ; inv-left → ctx 1
                ; inv-right → ctx 1
              }
  ; eq-lhs = λ{ mul-assoc → x ∗ y ∗ z
                ; e-left → e' ∗ a
                ; e-right → a ∗ e'
                ; inv-left → a ⁱ ∗ a
                ; inv-right → a ∗ a ⁱ
              }
  ; eq-rhs = λ{ mul-assoc → x ∗ (y ∗ z)
                ; e-left → a
                ; e-right → a
                ; inv-left → e'
                ; inv-right → e'
              }
  }
  where
  x : Term {Σ} (ctx 3)
  y : Term {Σ} (ctx 3)
  z : Term {Σ} (ctx 3)
  a : Term {Σ} (ctx 1)
  x = tm-var (var-inl (var-inl (var-inr var-var)))
  y = tm-var (var-inl (var-inr var-var))
  z = tm-var (var-inr var-var)
  a = tm-var (var-inr var-var)

open Theory 𝒢


e-left-eq : (ctx 1) ⊢ e' ∗ (tm-var (var-inr var-var)) ≈ (tm-var (var-inr var-var))
e-left-eq = eq-axiom {!e-left!} id-substitution


