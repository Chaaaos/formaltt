module SingleSorted.Groups where

open import SingleSorted.AlgebraicTheory
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin
import Agda.Primitive
open import SingleSorted.Substitution

data GroupOper : Set where
  e : GroupOper
  inv : GroupOper
  mul : GroupOper

-- groupsₛ : Signature
-- groupsₛ =
--   record
--   { oper = GroupOper
--   ; oper-arity = λ{ e → 0 ; inv → 1 ; mul → 2}
--   }

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

-- _ : Term {groupsₛ} 0
-- _ = e'

-- _ : Term {groupsₛ} 2
-- _ = tm-var Fin.zero


-- -- define some names for variables to make life easier
-- x' : Term {groupsₛ} 2
-- x' = tm-var zero

-- y' : Term {groupsₛ} 2
-- y' = tm-var (Fin.suc Fin.zero)

-- -- x and y are terms in the context (x, y)

-- -- construct some example terms
-- _ : Term {groupsₛ} 2
-- _ = inv' x'

-- _ : Term {groupsₛ} 2
-- _ = mul' x' y'

-- _ : Term {groupsₛ} 2
-- _ = x' ∗ y'

-- _ : Term {groupsₛ} 2
-- _ = (x' ∗ y' ⁱ ∗ x') ⁱ

-- -- now we want to define the properties that hold for group operations
-- -- how to we define this for any good context
-- -- probably via substitution
-- data GroupEq : Set where
--    mul-assoc e-left e-right inv-left inv-right : GroupEq

-- x : Term {groupsₛ} 3
-- x = tm-var zero

-- y : Term {groupsₛ} 3
-- y = tm-var (suc zero)

-- z : Term {groupsₛ} 3
-- z = tm-var (suc (suc zero))

-- a : Term {groupsₛ} 1
-- a = tm-var zero

-- groupsₜ : Theory Agda.Primitive.lzero groupsₛ
-- groupsₜ = record
--             { eq = GroupEq
--             ; eq-ctx = λ{ mul-assoc → 3; e-left → 1; e-right → 1; inv-left → 1; inv-right → 1}
--             ; eq-lhs =
--               λ{ mul-assoc → x ∗ y ∗ z
--                 ; e-left → e' ∗ a
--                 ; e-right → a ∗ e'
--                 ; inv-left → a ⁱ ∗ a
--                 ; inv-right → a ∗ a ⁱ
--                 }
--             ; eq-rhs = 
--               λ{ mul-assoc → x ∗ (y ∗ z)
--                 ; e-left → a
--                 ; e-right → a
--                 ; inv-left → e'
--                 ; inv-right → e'
--                 }
--             }

-- open Theory groupsₜ

-- this is 0 as an element of [1] injected into [2] as 0
-- here [n] := {0, 1, 2, ..., n-1}
-- _ : Fin 2
-- _ = lift-prod₂ {Agda.Primitive.lzero} {groupsₛ} groupsₜ {1} {1} zero

-- xˣʸ : Fin 2
-- xˣʸ = lift-prod₂ {Agda.Primitive.lzero} {groupsₛ} groupsₜ {1} {1} zero

-- -- this is 0 as an element of [1] injected into [2] as 1
-- yˣʸ : Fin 2
-- yˣʸ = lift-prod₁ {Agda.Primitive.lzero} {groupsₛ} groupsₜ {1} {1} zero

-- _ : Fin 3
-- _ = lift-prod₁ {Agda.Primitive.lzero} {groupsₛ} groupsₜ {1} {2} zero

-- _ : Fin 3
-- _ = lift-prod₁ {Agda.Primitive.lzero} {groupsₛ} groupsₜ {1} {2} (suc zero)

-- i : substitution groupsₛ 2 1
-- i = λ{ x → tm-var (lift-prod₂ {Agda.Primitive.lzero} {groupsₛ} groupsₜ {1} {1} x)}

-- j : substitution groupsₛ 2 1
-- j = λ{ x → tm-var (lift-prod₁ {Agda.Primitive.lzero} {groupsₛ} groupsₜ {1} {1} x)}

-- eq1 : Theory.eq groupsₜ
-- eq1 = e-left

-- add-variable : ∀ {Γ : Context} → substitution groupsₛ (Γ Data.Nat.+ 1) Γ
-- add-variable = {!!}


-- e-right-ctx1 : 1 ⊢ a ∗ e' ≈ a
-- e-right-ctx1 =  eq-id-action groupsₜ (eq-axiom e-right {1} id-substitution)



-- weakening : ∀ {Γ : Context} {u v : Term Γ} -- {σ : substitution groupsₛ (Γ Data.Nat.+ 1) Γ}
--   → Γ ⊢ u ≈ v
--   -------------------------------------------------
--   → (Γ Data.Nat.+ 1) ⊢ u [ add-variable ]s ≈ v [ add-variable ]s
-- weakening Theory.eq-refl = Theory.eq-refl
-- weakening (Theory.eq-symm eq₁) = Theory.eq-symm (weakening eq₁)
-- weakening (Theory.eq-tran eq₁ eq₂) = Theory.eq-tran (weakening eq₁) (weakening eq₂)
-- weakening (Theory.eq-congr eqᵢ) = Theory.eq-congr  λ{ op →  weakening (eqᵢ op)}
-- weakening (Theory.eq-axiom mul-assoc σ) = {!!}
-- weakening (Theory.eq-axiom e-left σ) = {!!}
-- weakening (Theory.eq-axiom e-right σ) = {!!}
-- weakening (Theory.eq-axiom inv-left σ) = {!!}
-- weakening (Theory.eq-axiom inv-right σ) = {!!}
