open import SingleSorted.AlgebraicTheory

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
ctx-2 = ctx-concat ctx-slot ctx-slot

ctx : ∀ (n : ℕ) → Context
ctx zero = ctx-empty
ctx (suc n) = ctx-concat (ctx n) ctx-slot

Σ : Signature
Σ = record { oper = GroupOp ; oper-arity = λ{ e → ctx-empty ; inv → ctx-1 ; mul → ctx-2} }

_ : Term {Σ} ctx-1
_ = tm-var var-var

y : Term {Σ} ctx-2
y = tm-var (var-inr var-var)

x : Term {Σ} ctx-2
x = tm-var (var-inr var-var)

xy : Term {Σ} ctx-2
xy = tm-oper mul (λ{ (var-inl x₁) → x ; (var-inr y₁) → y})


mul' : ∀ (Γ : Context) → Term {Σ} Γ → Term {Σ} Γ → Term {Σ} Γ
mul' Γ t₁ t₂ = {!!}


-- mul' : ∀ {Γ} → Term {groupsₛ} Γ → Term {groupsₛ} Γ → Term {groupsₛ} Γ
-- mul' x y = tm-oper mul λ{ Fin.zero → x ; (Fin.suc Fin.zero) → y}

-- inv' : ∀ {Γ} → Term {groupsₛ} Γ → Term {groupsₛ} Γ
-- inv' x = tm-oper inv λ{ Fin.zero → x}

-- e' : ∀ {Γ} → Term {groupsₛ} Γ
-- e' = tm-oper e λ()


-- _∗_ : ∀ {Γ} → Term {groupsₛ} Γ → Term {groupsₛ} Γ → Term {groupsₛ} Γ
-- x ∗ y = mul' x y

-- _ⁱ : ∀ {Γ} → Term {groupsₛ} Γ → Term {groupsₛ} Γ
-- x ⁱ = inv' x


-- infixl 5 _∗_
-- infix 6 _ⁱ
