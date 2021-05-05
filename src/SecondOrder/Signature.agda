open import Agda.Primitive using (lzero; lsuc; _⊔_)

import SecondOrder.Arity
import SecondOrder.Context

module SecondOrder.Signature {ℓs ℓo ℓa} (𝔸 : SecondOrder.Arity.Arity) where
  open SecondOrder.Arity.Arity 𝔸

  -- a second-order algebraic signature
  record Signature : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where

    -- a signature consists of a set of sorts and a set of operations
    -- e.g. sorts A, B, C, ... and operations f, g, h
    field
      sort : Set ℓs -- sorts
      oper : Set ℓo -- operations

    open SecondOrder.Context sort public

    -- each operation has arity and a sort (the sort of its codomain)
    field
      oper-arity : oper → arity -- the arity of an operation
      oper-sort : oper → sort -- the operation sort
      arg-sort : ∀ (f : oper) → arg (oper-arity f) → sort -- the sorts of arguments
      -- a second order operation can bind some free variables that occur as its arguments
      -- e.g. the lambda operation binds one type and one term
      arg-bind : ∀ (f : oper) → arg (oper-arity f) → Context -- the argument bindings

    -- the arguments of an operation
    oper-arg : oper → Set
    oper-arg f = arg (oper-arity f)
