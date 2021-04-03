open import SingleSorted.AlgebraicTheory
open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SingleSorted.Substitution
open import Data.Nat using (ℕ; zero; suc)

module SingleSorted.Ring where

open import SingleSorted.Group as Group using (GroupOp; e; inv; mul)

open GroupOp

data RingOp : Set where
  id-mul : RingOp
  id-sum : RingOp
  minus : RingOp
  mult : RingOp
  sum : RingOp

groupToRingOp : GroupOp → RingOp
groupToRingOp e = id-sum
groupToRingOp inv = minus
groupToRingOp mul = sum

ctx : ∀ (n : ℕ) → Context
ctx zero = ctx-empty
ctx (suc n) = ctx-concat (ctx n) ctx-slot

-- the signature of the theory of groups
-- has one constant, one unary operation, one binary operation
Σ : Signature
Σ = record { oper = RingOp
           ; oper-arity = λ{ id-mul → ctx 0
                           ; id-sum → ctx 0
                           ; minus → ctx 1
                           ; mult → ctx 2
                           ; sum → ctx 2
                           }
            }

open Signature Σ

-- helper functions for creating terms
zero' : ∀ {Γ : Context} → Term Γ
zero' = tm-oper id-sum λ()

one : ∀ {Γ : Context} → Term Γ
one = tm-oper id-mul λ()

concat-empty : var (ctx-concat ctx-empty ctx-slot) → (var ctx-slot)
concat-empty (var-inr x) = x

singleton-context : (var ctx-slot) → var (ctx-concat ctx-empty ctx-slot)
singleton-context (var-var) = var-inr var-var

σ : ∀ {Γ : Context} {t : Term Γ} →  Γ ⇒s (ctx 1)
σ {Γ} {t} = λ{ (var-inr var-var) → t}

δ : ∀ {Γ : Context} {t : Term Γ} {s : Term Γ} →   Γ ⇒s (ctx 2)
δ {Γ} {t} {s} = λ{ (var-inl x) → t ; (var-inr y) → s}

_∗_ : ∀ {Γ} → Term Γ → Term Γ → Term Γ
t ∗ s =  tm-oper mult λ{ xs → δ {t = t} {s = s} xs}

_+_ : ∀ {Γ} → Term Γ → Term Γ → Term Γ
t + s = tm-oper sum λ{ xs → δ {t = t} {s = s} xs}

-_ : ∀ {Γ : Context} →  Term Γ → Term Γ
- t =  tm-oper minus λ{ x → σ {t = t} x}

infixl 4 _+_
infixl 5 _∗_
infix 6 -_

_ : Term (ctx 2)
_ = tm-var (var-inl (var-inr var-var)) ∗ tm-var (var-inr var-var) + tm-var (var-inr var-var)


-- (+, zero') form an Abelian group
-- Group-+ : T

-- group equations
data RingEq : Set where
  +-assoc 0-inv-+-right 0-unit-+-left 0-unit-+-right 0-inv-+-left -inv-left -inv-right : RingEq
  mul-assoc 1-unit-∗-left 1-unit-∗-right : RingEq
  ∗-distrib-+-left ∗-distrib-+-right : RingEq
  

groupToRingEq : Group.GroupEq → RingEq
groupToRingEq Group.mul-assoc = +-assoc
groupToRingEq Group.e-left = 0-unit-+-left
groupToRingEq Group.e-right = 0-unit-+-right
groupToRingEq Group.inv-left = -inv-left
groupToRingEq Group.inv-right = -inv-right


+-assoc-ax : Equation
+-assoc-ax = record { eq-ctx = Signature.Equation.eq-ctx Group.mul-assoc-ax
                    ; eq-lhs = Signature.Equation.eq-lhs {!Group.mul-assoc-ax!}
                    ; eq-rhs = {!!}
                    }

-- e-left-ax : Axiom
-- e-right-ax : Axiom
-- inv-left-ax : Axiom
-- inv-right-ax : Axiom

-- mul-assoc-ax = record { eq-ctx = ctx 3
--                       ; eq-lhs = x ∗ y ∗ z
--                       ; eq-rhs = x ∗ (y ∗ z)
--                       }
--              where
--              x : Term (ctx 3)
--              y : Term (ctx 3)
--              z : Term (ctx 3)
--              x = tm-var (var-inl (var-inl (var-inr var-var)))
--              y = tm-var (var-inl (var-inr var-var))
--              z = tm-var (var-inr var-var)

-- e-left-ax = record { eq-ctx = ctx 1 ; eq-lhs = e' ∗ x ; eq-rhs = x }
--   where
--   x : Term (ctx 1)
--   x = tm-var (var-inr var-var)

-- e-right-ax = record { eq-ctx = ctx 1 ; eq-lhs = x ∗ e' ; eq-rhs = x }
--   where
--   x : Term (ctx 1)
--   x = tm-var (var-inr var-var)


-- inv-left-ax = record { eq-ctx = ctx 1 ; eq-lhs = x ⁱ ∗ x ; eq-rhs = e' }
--   where
--   x : Term (ctx 1)
--   x = tm-var (var-inr var-var)

-- inv-right-ax = record { eq-ctx = ctx 1 ; eq-lhs = x ∗ x ⁱ ; eq-rhs = e' }
--   where
--   x : Term (ctx 1)
--   x = tm-var (var-inr var-var)


𝒢 : Theory lzero Σ
𝒢 = record { ax = RingEq
            ; ax-eq = λ{ mul-assoc → {!Group.mul-assoc-ax!}
                       ; e-left → {!!}
                       ; e-right → {!!}
                       ; inv-left → {!!}
                       ; inv-right → {!!}
                       }
            }
