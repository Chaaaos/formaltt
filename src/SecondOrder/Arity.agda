import Data.Empty
import Data.Unit
import Data.Bool
import Data.Nat
import Data.Fin

module SecondOrder.Arity where

  -- A notion of arity is given by a set of possible arities, and a mapping which to each arity assings a set of
  -- argument positions.

  record Arity : Set₁ where
    field
      arity : Set -- the set of permissible arities, e.g., ℕ for finitary arities
      arg : arity → Set -- every arity gives a set of argument (position), e.g. Fin

  -- finitary arities
  arity-finite : Arity
  arity-finite = record { arity = Data.Nat.ℕ ; arg = Data.Fin.Fin }

  module Arity012 where
    -- For example, in algebra we quite often only consider constants, unary and binary
    -- operations. Thus we would only need three arities.

    data arity012 : Set where
      Constant Unary Binary : arity012

    arg012 : arity012 → Set
    arg012 Constant = Data.Empty.⊥
    arg012 Unary = Data.Unit.⊤
    arg012 Binary = Data.Bool.Bool

    arity-012 : Arity
    arity-012 = record { arity =  arity012 ; arg = arg012 }
